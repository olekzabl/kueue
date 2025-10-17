package tas

import (
	"bytes"
	"compress/gzip"
	"encoding/base64"
	"encoding/json"
	"fmt"
	"slices"
	"sort"
	"strconv"
	"strings"
	"testing"

	"github.com/google/uuid"
	kueue "sigs.k8s.io/kueue/apis/kueue/v1beta1"
)

// === UTILITY FUNCTIONS ===

// Distribute given number of nodes among given number of pools.
// The 1st pool gets ~half of all nodes, 2nd pool ~quarter of all etc.
// However, we pay attention that every pool should have at least 1 node.
// The result is sorted non-ascending.
func nodePoolSizes(nodes, pools int) []int {
	free := nodes

	// Leave at least 1 node for each pool
	next := nodes - pools
	next /= 2

	res := make([]int, pools)
	for i := range pools {
		res[i] = next
		free -= next
		next /= 2
		if next == 0 {
			next = 1
		}
	}

	for i := range free {
		res[i%pools] += 1
	}

	return res
}

// Generate n "UUID"s (hex numbers) of given length,
// ensuring they're distinct (and otherwise random).
func uuids(n, length int) []string {
	m := map[string]bool{}
	res := make([]string, n)
	for i := range n {
		for {
			fullId := uuid.New().String()
			id := fullId[len(fullId)-length:]
			if !m[id] {
				m[id] = true
				res[i] = id
				break
			}
		}
	}
	return res
}

// Return an array of ones, of given size.
func ones(length int) []int32 {
	res := make([]int32, length)
	for i := range res {
		res[i] = 1
	}
	return res
}

func ipPartFromHex(s string) int {
	res, err := strconv.ParseInt(strings.ToUpper(s), 16, 32)
	if err != nil {
		panic(err)
	}
	return int(res)
}

func jsonStr(v any) string {
	bytes, err := json.Marshal(v)
	if err != nil {
		panic(err)
	}
	return string(bytes)
}

func jsonPretty(v any, indent int) string {
	bytes, err := json.MarshalIndent(v, strings.Repeat(" ", indent), "  ")
	if err != nil {
		panic(err)
	}
	return string(bytes)
}

// === NAMING SCHEMES ===

type namingScheme func(nodes, pools int) []string

func gkeNaming(clusterName, poolNamePrefix string) namingScheme {
	return func(nodes, pools int) []string {
		res := make([]string, nodes)
		pos := 0
		poolIds := uuids(2*pools, 8)
		for i, size := range nodePoolSizes(nodes, pools) {
			nodeIds := uuids(size, 4)
			for j, nodeId := range nodeIds {
				res[pos] = fmt.Sprintf(
					"gke-%s-%s%d-%s-%s",
					clusterName,
					poolNamePrefix,
					i,
					poolIds[2*i+j/(size/2+1)],
					nodeId,
				)
				pos++
			}
		}
		return res
	}
}

func aksNaming(poolNamePrefix string) namingScheme {
	return func(nodes, pools int) []string {
		res := make([]string, nodes)
		pos := 0
		poolIds := uuids(pools, 8)
		for i, size := range nodePoolSizes(nodes, pools) {
			for j := range size {
				res[pos] = fmt.Sprintf(
					"aks-%s%d-%s-%06s",
					poolNamePrefix,
					i,
					poolIds[i],
					strings.ToUpper(strconv.FormatInt(int64(j), 36)),
				)
				pos++
			}
		}
		return res
	}
}

func eksNaming(nodes, pools int) []string {
	// Some EKS locations, just to have sth to pick from
	var regions = []string{
		"ap-northeast-3",
		"us-east-2",
		"ap-southeast-1",
		"us-east-1",
		"ca-central-1",
		"eu-west-1",
		"ap-northeast-2",
		"us-west-2",
		"us-west-1",
		"ap-south-1",
		"ap-southeast-2",
		"ap-northeast-1",
		"eu-central-1",
		"eu-west-2",
		"eu-west-3",
		"sa-east-1",
	}
	res := make([]string, nodes)
	pos := 0
	ips := uuids(nodes, 4)
	for i, size := range nodePoolSizes(nodes, pools) {
		loc := regions[i%len(regions)]
		for range size {
			res[pos] = fmt.Sprintf(
				"ip-10-0-%d-%d.%s.compute.internal",
				ipPartFromHex(ips[pos][:2]),
				ipPartFromHex(ips[pos][2:]),
				loc,
			)
			pos++
		}
	}
	return res
}

// === TRIE STUFF ===

type TrieNode struct {
	hasWord  bool
	children map[byte]*TrieNode
	size     int
	split    bool
}

func newTrieNode() *TrieNode {
	return &TrieNode{
		children: map[byte]*TrieNode{},
	}
}

func (n *TrieNode) add(name []byte) {
	n.size += 1
	if len(name) == 0 {
		n.hasWord = true
	} else {
		next := name[0]
		if n.children[next] == nil {
			n.children[next] = newTrieNode()
		}
		n.children[next].add(name[1:])
	}
}

func (n *TrieNode) setSplits(L int) (gain int) {
	if n.size < L*(len(n.children)-1) {
		return 0
	}
	n.split = true
	gain += n.size - L*(len(n.children)-1)
	for _, child := range n.children {
		gain += child.setSplits(L)
	}
	return gain
}

func (n *TrieNode) getStringsInternal(history string, dir direction, res *[]string) {
	if n.hasWord {
		if dir == prefixDir {
			*res = append(*res, history)
		} else {
			*res = append(*res, reverse(history))
		}
	}
	for c, child := range n.children {
		child.getStringsInternal(history+string(c), dir, res)
	}
}

func (n *TrieNode) getStrings(dir direction) []string {
	res := make([]string, 0, n.size)
	n.getStringsInternal("", dir, &res)
	return res
}

func (n *TrieNode) getGroups(history string, dir direction, alsoAdd string) (res []*PrefixSuffixBasedGroup) {
	if !n.split {
		res := &PrefixSuffixBasedGroup{
			NodeNames: n.getStrings(dir),
			Counts:    ones(n.size),
		}
		if dir == prefixDir {
			res.NodeNamePrefix = history
			res.NodeNameSuffix = alsoAdd
		} else {
			res.NodeNameSuffix = reverse(history)
			res.NodeNamePrefix = alsoAdd
		}
		return []*PrefixSuffixBasedGroup{res}
	} else {
		for c, child := range n.children {
			res = append(res, child.getGroups(history+string(c), dir, alsoAdd)...)
		}
		return
	}
}

// === ENCODINGS ===

var (
	hostOnly = []string{"kubernetes.io/hostname"}
)

type encoding func(nodes []string) any

// --- Original ---

func original(nodes []string) any {
	domains := make([]kueue.TopologyDomainAssignment, 0, len(nodes))
	for _, name := range nodes {
		domains = append(domains, kueue.TopologyDomainAssignment{
			Values: []string{name},
			Count:  1,
		})
	}
	return &kueue.TopologyAssignment{
		Levels:  hostOnly,
		Domains: domains,
	}
}

// --- Compact V1 ---

type CompactV1 struct {
	Levels    []string
	NodeNames []string
	Counts    []int32
}

func compactV1(nodes []string) any {
	return &CompactV1{
		Levels:    hostOnly,
		NodeNames: nodes,
		Counts:    ones(len(nodes)),
	}
}

// --- Compact V1 + GZIP ---

type CompactV1Gzip struct {
	Levels           []string
	NodeNamesGzipped string
	Counts           []int32
}

func compactV1GzipHex(nodes []string) any {
	var buf bytes.Buffer
	zw := gzip.NewWriter(&buf)
	bytes, _ := json.Marshal(nodes)
	zw.Write(bytes)
	zw.Close()
	return &CompactV1Gzip{
		Levels:           hostOnly,
		NodeNamesGzipped: fmt.Sprintf("%x", buf.String()),
		Counts:           ones(len(nodes)),
	}
}

func compactV1GzipBase64(nodes []string) any {
	var buf bytes.Buffer
	zw := gzip.NewWriter(&buf)
	bytes, _ := json.Marshal(nodes)
	zw.Write(bytes)
	zw.Close()

	return &CompactV1Gzip{
		Levels:           hostOnly,
		NodeNamesGzipped: base64.StdEncoding.EncodeToString(buf.Bytes()),
		Counts:           ones(len(nodes)),
	}
}

type PrefixBased struct {
	Levels []string
	Groups []*PrefixBasedGroup
}

type PrefixBasedGroup struct {
	NodeNamePrefix string `json:",omitempty"`
	NodeNames      []string
	Counts         []int32
}

type PrefixSuffixBased struct {
	Levels []string
	Groups []*PrefixSuffixBasedGroup
}

type PrefixSuffixBasedGroup struct {
	NodeNamePrefix string `json:",omitempty"`
	NodeNameSuffix string `json:",omitempty"`
	NodeNames      []string
	Counts         []int32
}

// --- Elastic prefix ---

func elasticPrefix(L int) encoding {
	return func(nodes []string) any {
		root := newTrieNode()
		for _, name := range nodes {
			root.add([]byte(name))
		}
		root.setSplits(L)
		return &PrefixSuffixBased{
			Levels: hostOnly,
			Groups: root.getGroups("", prefixDir, ""),
		}
	}
}

func elasticPrefixOrSuffix(L int) encoding {
	return func(nodes []string) any {
		rootP := newTrieNode()
		for _, name := range nodes {
			rootP.add([]byte(name))
		}
		gainP := rootP.setSplits(L)

		rootS := newTrieNode()
		for _, name := range nodes {
			rootS.add([]byte(reverse(name)))
		}
		gainS := rootS.setSplits(L)

		// fmt.Printf("Gains: %d, %d\n", gainP, gainS)
		if gainP >= gainS {
			return &PrefixSuffixBased{
				Levels: hostOnly,
				Groups: rootP.getGroups("", prefixDir, ""),
			}
		} else {
			return &PrefixSuffixBased{
				Levels: hostOnly,
				Groups: rootS.getGroups("", suffixDir, ""),
			}
		}
	}
}

func elasticSymmetricPlusSingle(L int, withPunct bool) encoding {
	return func(nodes []string) any {
		suffix := singleSuffix(nodes, withPunct)
		rootP := newTrieNode()
		for _, name := range nodes {
			rootP.add([]byte(name[:len(name)-len(suffix)]))
		}
		gainP := rootP.setSplits(L)

		prefix := singlePrefix(nodes, withPunct)
		rootS := newTrieNode()
		for _, name := range nodes {
			rootS.add([]byte(reverse(name[len(prefix):])))
		}
		gainS := rootS.setSplits(L)

		// fmt.Printf("Gains: %d, %d\n", gainP, gainS)
		if gainP >= gainS {
			return &PrefixSuffixBased{
				Levels: hostOnly,
				Groups: rootP.getGroups("", prefixDir, suffix),
			}
		} else {
			return &PrefixSuffixBased{
				Levels: hostOnly,
				Groups: rootS.getGroups("", suffixDir, prefix),
			}
		}
	}
}

// --- Uniform prefix ---

type direction int

const (
	prefixDir = iota
	suffixDir
)

func reverse(s string) string {
	// return s
	bytes := []byte(s)
	slices.Reverse(bytes)
	return string(bytes)
}

func uniformPrefixInternal(nodes []string, dir direction, L int) (res PrefixSuffixBased, prefixLen int) {
	var nodesCopy []string
	if dir == prefixDir {
		nodesCopy = nodes[:]
	} else {
		nodesCopy = make([]string, 0, len(nodes))
		for _, node := range nodes {
			nodesCopy = append(nodesCopy, reverse(node))
		}
	}

	sort.Strings(nodesCopy)
	flipsAt := make([]int, 300)
	for i := range len(nodesCopy) - 1 {
		curr := nodesCopy[i]
		next := nodesCopy[i+1]
		for j := 0; j < len(curr) && j < len(next); j++ {
			if curr[j] != next[j] {
				flipsAt[j] += 1
				break
			}
		}
	}

	cum := 1
	prefixLen = 0
	for i := 0; i < len(flipsAt); i++ {
		// fmt.Printf("at %d: %d flips; %d*%d >? %d\n", i, flipsAt[i], flipsAt[i], L+i, len(nodes))
		if flipsAt[i]*(L+i) > len(nodes) {
			break
		}
		cum += flipsAt[i]
		prefixLen++
	}
	// fmt.Printf("Prefix length: %d\n", prefixLen)

	r := PrefixSuffixBased{
		Levels: hostOnly,
		Groups: make([]*PrefixSuffixBasedGroup, 0, cum),
	}
	prevHead := ""
	var group *PrefixSuffixBasedGroup
	for _, name := range nodesCopy {
		cut := prefixLen
		if cut > len(name) {
			cut = len(name)
		}
		head := name[:cut]
		tail := name[cut:]
		if dir == suffixDir {
			head = reverse(head)
			tail = reverse(tail)
		}
		if head != prevHead {
			if group != nil {
				r.Groups = append(r.Groups, group)
			}
			group = &PrefixSuffixBasedGroup{}
			if dir == prefixDir {
				group.NodeNamePrefix = head
			} else {
				group.NodeNameSuffix = head
			}
		}
		group.NodeNames = append(group.NodeNames, tail)
		group.Counts = append(group.Counts, 1)
		prevHead = head
	}
	r.Groups = append(r.Groups, group)
	return r, prefixLen
}

func uniformPrefixAndSingleSuffix(L int) encoding {
	return func(nodes []string) any {
		suffix := nodes[0]
		for i, name := range nodes {
			if i == 0 {
				continue
			}
			n := len(name)
			if n < len(suffix) {
				suffix = suffix[len(suffix)-n:]
			}
			for j := 1; j <= len(suffix); j++ {
				if name[n-j] != suffix[len(suffix)-j] {
					suffix = suffix[len(suffix)-j+1:]
					break
				}
			}
		}

		nodesCopy := nodes[:]

		sort.Strings(nodesCopy)
		flipsAt := make([]int, 300)
		for i := range len(nodesCopy) - 1 {
			curr := nodesCopy[i]
			next := nodesCopy[i+1]
			for j := 0; j < len(curr) && j < len(next); j++ {
				if curr[j] != next[j] {
					flipsAt[j] += 1
					break
				}
			}
		}

		cum := 1
		prefixLen := 0
		for i := 0; i < len(flipsAt); i++ {
			// fmt.Printf("at %d: %d flips; %d*%d >? %d\n", i, flipsAt[i], flipsAt[i], L+i, len(nodes))
			if flipsAt[i]*(L+i) > len(nodes) {
				break
			}
			cum += flipsAt[i]
			prefixLen++
		}
		// fmt.Printf("Prefix length: %d\n", prefixLen)

		r := PrefixSuffixBased{
			Levels: hostOnly,
			Groups: make([]*PrefixSuffixBasedGroup, 0, cum),
		}
		prevHead := ""
		var group *PrefixSuffixBasedGroup
		for _, name := range nodesCopy {
			cut := prefixLen
			if cut > len(name) {
				cut = len(name)
			}
			head := name[:cut]
			tail := name[cut:]
			if head != prevHead {
				if group != nil {
					r.Groups = append(r.Groups, group)
				}
				group = &PrefixSuffixBasedGroup{}
				group.NodeNamePrefix = head
				group.NodeNameSuffix = name[len(name)-len(suffix):]
			}
			group.NodeNames = append(group.NodeNames, tail[:len(tail)-len(suffix)])
			group.Counts = append(group.Counts, 1)
			prevHead = head
		}
		r.Groups = append(r.Groups, group)
		return r
	}
}

func compareBytes(a, b byte) int {
	if a < b {
		return -1
	}
	if a > b {
		return 1
	}
	return 0
}

func compareRev(a, b string) int {
	la := len(a)
	lb := len(b)
	for j := 1; j <= la && j <= lb; j++ {
		if diff := compareBytes(a[la-j], b[lb-j]); diff != 0 {
			return int(diff)
		}
	}
	return 0
}

func uniformSuffixInternal(nodes []string, L int) (res PrefixSuffixBased, prefixLen int) {
	nodesCopy := nodes[:]
	slices.SortFunc(nodesCopy, compareRev)
	flipsAt := make([]int, 300)
	for i := range len(nodesCopy) - 1 {
		curr := nodesCopy[i]
		next := nodesCopy[i+1]
		lc := len(curr)
		ln := len(next)
		for j := 1; j <= lc && j <= ln; j++ {
			if curr[lc-j] != next[ln-j] {
				flipsAt[j] += 1
				break
			}
		}
	}

	cum := 1
	prefixLen = 0
	for i := 1; i < len(flipsAt); i++ {
		// fmt.Printf("at %d: %d flips; %d*%d >? %d\n", i, flipsAt[i], flipsAt[i], L+i, len(nodes))
		if flipsAt[i]*(L+i) > len(nodes) {
			break
		}
		cum += flipsAt[i]
		prefixLen++
	}
	// fmt.Printf("Prefix length: %d\n", prefixLen)

	r := PrefixSuffixBased{
		Levels: hostOnly,
		Groups: make([]*PrefixSuffixBasedGroup, 0, cum),
	}
	prevHead := ""
	var group *PrefixSuffixBasedGroup
	for _, name := range nodesCopy {
		cut := prefixLen
		if cut > len(name) {
			cut = len(name)
		}
		head := name[len(name)-cut:]
		tail := name[:len(name)-cut]
		if head != prevHead || group == nil {
			if group != nil {
				r.Groups = append(r.Groups, group)
			}
			group = &PrefixSuffixBasedGroup{}
			group.NodeNameSuffix = head
		}
		group.NodeNames = append(group.NodeNames, tail)
		group.Counts = append(group.Counts, 1)
		prevHead = head
	}
	r.Groups = append(r.Groups, group)
	return r, prefixLen
}

func naiveSuffixInternal(nodes []string, C int) (res PrefixSuffixBased, suffixLen int) {
	m := make([][]bool, 300)
	for i := range len(m) {
		m[i] = make([]bool, 256)
	}
	for _, name := range nodes {
		n := len(name)
		for i, b := range name {
			m[n-i][b] = true
		}
	}

	for j := 1; j < 300; j++ {
		cnt := 0
		for _, flag := range m[j] {
			if flag {
				cnt++
			}
		}
		if cnt > C {
			break
		}
		suffixLen++
	}

	sm := map[string]*PrefixSuffixBasedGroup{}
	for _, name := range nodes {
		n := len(name)
		head := name[n-suffixLen:]
		tail := name[:n-suffixLen]
		if sm[head] == nil {
			sm[head] = &PrefixSuffixBasedGroup{
				NodeNameSuffix: head,
			}
		}
		sm[head].NodeNames = append(sm[head].NodeNames, tail)
		sm[head].Counts = append(sm[head].Counts, 1)
	}

	res = PrefixSuffixBased{
		Levels: hostOnly,
		Groups: make([]*PrefixSuffixBasedGroup, 0, len(sm)),
	}
	for _, g := range sm {
		res.Groups = append(res.Groups, g)
	}
	return
}

func isPunct(b byte) bool {
	return b == '.' || b == '-'
}

func singlePrefix(nodes []string, withPunct bool) string {
	prefix := nodes[0]
	for i, name := range nodes {
		if i == 0 {
			continue
		}
		n := len(name)
		if n < len(prefix) {
			prefix = prefix[:n]
		}
		for j := 0; j < len(prefix); j++ {
			if name[j] != prefix[j] {
				prefix = prefix[:j]
				break
			}
		}
		if withPunct {
			for len(prefix) > 0 && !isPunct(prefix[len(prefix)-1]) {
				prefix = prefix[:len(prefix)-1]
			}
		}
	}
	return prefix
}

func singleSuffix(nodes []string, withPunct bool) string {
	suffix := nodes[0]
	for i, name := range nodes {
		if i == 0 {
			continue
		}
		n := len(name)
		if n < len(suffix) {
			suffix = suffix[len(suffix)-n:]
		}
		for j := 1; j <= len(suffix); j++ {
			if name[n-j] != suffix[len(suffix)-j] {
				suffix = suffix[len(suffix)-j+1:]
				break
			}
		}
		if withPunct {
			for len(suffix) > 0 && !isPunct(suffix[0]) {
				suffix = suffix[1:]
			}
		}
	}
	return suffix
}

func singlePrefixAndSuffix(withPunct bool) encoding {
	return func(nodes []string) any {
		prefix := singlePrefix(nodes, withPunct)
		suffix := singleSuffix(nodes, withPunct)
		roots := make([]string, 0, len(nodes))
		for _, name := range nodes {
			roots = append(roots, name[len(prefix):len(name)-len(suffix)])
		}
		return PrefixSuffixBased{
			Levels: hostOnly,
			Groups: []*PrefixSuffixBasedGroup{{
				NodeNamePrefix: prefix,
				NodeNameSuffix: suffix,
				NodeNames:      roots,
				Counts:         ones(len(nodes)),
			}},
		}
	}
}

func uniformPrefix(L int) encoding {
	return func(nodes []string) any {
		res, _ := uniformPrefixInternal(nodes, prefixDir, L)
		return res
	}
}

func uniformPrefixOrSuffix(L int) encoding {
	return func(nodes []string) any {
		p, pl := uniformPrefixInternal(nodes, prefixDir, L)
		s, sl := uniformSuffixInternal(nodes, L)
		if pl >= sl {
			return p
		} else {
			return s
		}
	}
}

func uniformPrefixOrNaiveSuffix(L int, C int) encoding {
	return func(nodes []string) any {
		p, pl := uniformPrefixInternal(nodes, prefixDir, L)
		s, sl := naiveSuffixInternal(nodes, C)
		if pl >= sl {
			return p
		} else {
			return s
		}
	}
}

// --- Uniform prefix or suffix

// === RUNNING SIMULATIONS ===

type Named[T any] struct {
	Desc string
	Val  T
}

var (
	gkeHappyNaming = gkeNaming("cluster-1", "node-pool-")

	namings = []Named[namingScheme]{
		{"GKE X-short", gkeNaming("c", "")},
		{"GKE happy", gkeHappyNaming},
		{"AKS X-short", aksNaming("")},
		{"AKS happy", aksNaming("node-pool-")},
		{"EKS", eksNaming},
	}

	encodings = []Named[encoding]{
		// {"Original", original},
		// {"Parallel V1", compactV1},
		// {"Parallel V1 + GZIP->hex", compactV1GzipHex},
		// {"Parallel V1 + GZIP->base64", compactV1GzipBase64},
		{"EP-60", elasticPrefix(60)},
		{"EP-60 | ES-60", elasticPrefixOrSuffix(60)},
		{"(EP-60 & 1pS) | (1pP & ES-60)", elasticSymmetricPlusSingle(60, true)},
		// {"UP-50", uniformPrefix(50)},
		// {"UP-50 | US-50", uniformPrefixOrSuffix(50)},
		// {"UP-50 | NS-9", uniformPrefixOrNaiveSuffix(50, 9)},
		// {"1P & 1S", singlePrefixAndSuffix(false)},
		// {"1Pp & 1Sp", singlePrefixAndSuffix(true)},
		// {"UP-50 & 1S", uniformPrefixAndSingleSuffix(50)},
	}
)

func TestNaming(t *testing.T) {
	fmt.Printf("=== Naming schemes ===\n")
	for _, n := range namings {
		fmt.Printf("* Demo for %s:\n", n.Desc)
		for _, node := range n.Val(10, 3) {
			fmt.Printf("  - %s\n", node)
		}
	}
}

func TestEncoding(t *testing.T) {
	fmt.Printf("=== Encodings ===\n")
	for _, enc := range encodings {
		fmt.Printf("* Demo for %s:\n", enc.Desc)
		// fmt.Printf("  %s\n", jsonPretty(enc.Val(gkeHappyNaming(5, 2)), 2))
		// fmt.Printf("  %s\n", jsonPretty(enc.Val(gkeNaming("c", "p")(30, 5)), 2))
		fmt.Printf("  %s\n", jsonPretty(enc.Val(eksNaming(30, 5)), 2))
	}
}

func testDesc(encDesc, nDesc string, nodePools int) string {
	return fmt.Sprintf("%26s | %13s | %4d pools", encDesc, nDesc, nodePools)
}

func TestLimits(t *testing.T) {
	for _, enc := range encodings {
		for _, n := range namings {
			for _, nodePools := range []int{5, 1000} {
				td := testDesc(enc.Desc, n.Desc, nodePools)
				m := map[int]int{}
				for _, size := range []int{20, 30, 40} {
					s := jsonStr(enc.Val(n.Val(size*1000, nodePools)))
					m[size] = len(s)
					// fmt.Printf("[%s]   %dk nodes -> %d bytes\n", td, size, len(s))
				}
				skew := 2*m[30] - (m[20] + m[40])
				perNode := float32(m[40]-m[20]) / 20000
				fit := int(float32(1500000-m[40])/perNode + 40000)
				fmt.Printf("[%s] Limit: %d nodes (skew: %d)\n", td, fit, skew)
			}
		}
	}
}

func BenchmarkEncoding(b *testing.B) {
	for _, enc := range encodings {
		for _, n := range namings {
			for _, nodePools := range []int{5, 1000} {
				td := testDesc(enc.Desc, n.Desc, nodePools)
				nodes := n.Val(40_000, nodePools)
				b.Run(td, func(b *testing.B) {
					for b.Loop() {
						enc.Val(nodes)
					}
				})
			}
		}
	}
}
