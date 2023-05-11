package main

import (
	"math"
	"math/rand"
	"os"
	"strconv"
)

const epsilon float64 = 0.02

type Code int

const (
	RS Code = iota
	LRC
	Clay
)

type Strategy int

const (
	Greedy Strategy = iota
	Random
)

// (n,k) rs code, when the i_th node failes, the cost required to read data from the jth node
func get_element_for_rs_repair_matrix(n, k, i, j int) int {
	ret := 1
	if i == j {
		ret = 0
	}
	return ret
}

// (k,l,n - k) lrc code, which divides data into l groups, computing 1 local parity and n-k global parity.
// The element represent when the i_th node failes, the cost required to read data from the jth node
func get_element_for_lrc_repair_matrix(n, k, l, i, j int) int {
	ret := 1

	nodes_per_group := k / l
	broken_group := i / nodes_per_group
	my_group := j / nodes_per_group

	if my_group == broken_group {
		ret = 1
	} else {
		ret = 0
	}

	if broken_group == l {
		if my_group == broken_group {
			ret = 0
		} else {
			ret = 1
		}
	}

	if i == j {
		ret = 0
	}

	return ret
}

// (n,k,n-1) clay code, when the i_th node failes, the cost required to read data from the jth node
func get_element_for_clay_repair_matrix(n, k, i, j int) int {
	ret := 1
	if i == j {
		ret = 0
	}
	return ret
}

// Each placement contains the IDs of n nodes
type PlacementGroup []int

type PGID int

type DataPlacement struct {
	//All placementgroups
	Groups []PlacementGroup

	//Recovery load graph
	recovery_load_graph [][]int

	//Sum of the weights for a node in recovery graph
	wv []int

	//The pg_ids for each node
	pgs_on_disk [][]PGID

	//Number of nodes
	N int

	//The erasure code used
	code Code
	//Number of data nodes in a PG
	n int
	//Number of data nodes in a PG
	k int
	//Used for lrc code
	l int

	//Used to control the rate of new data put on the new device
	c int
	//Used to specify the nodes that are added during system expansion
	new_added_node map[int]int
}

func NewPlacement(N int, code Code, n, k, l, c int) DataPlacement {
	var ret DataPlacement
	ret.N = N
	ret.n = n
	ret.k = k
	ret.l = l
	ret.c = c
	ret.code = code

	ret.wv = make([]int, N)
	ret.Groups = make([]PlacementGroup, 0)

	ret.recovery_load_graph = make([][]int, N)
	for i := 0; i < N; i++ {
		ret.recovery_load_graph[i] = make([]int, N)
	}

	ret.pgs_on_disk = make([][]PGID, N)
	for i := 0; i < N; i++ {
		ret.pgs_on_disk[i] = make([]PGID, 0)
	}

	ret.new_added_node = make(map[int]int)

	return ret
}

func (placement *DataPlacement) get_element_for_repair_matrix(i, j int) int {
	if placement.code == RS {
		return get_element_for_rs_repair_matrix(placement.n, placement.k, i, j)
	} else if placement.code == LRC {
		return get_element_for_lrc_repair_matrix(placement.n, placement.k, placement.l, i, j)
	} else if placement.code == Clay {
		return get_element_for_clay_repair_matrix(placement.n, placement.k, i, j)
	}
	return 0
}

func (placement *DataPlacement) add_group(group PlacementGroup) {

	for j := 0; j < len(group); j++ {
		for t := 0; t < len(group); t++ {
			if j != t {
				placement.recovery_load_graph[group[j]][group[t]] += placement.get_element_for_repair_matrix(j, t)
				placement.wv[group[j]] += placement.get_element_for_repair_matrix(j, t)
				placement.wv[group[t]] += placement.get_element_for_repair_matrix(j, t)
			}
		}
	}

	for j := 0; j < len(group); j++ {
		placement.pgs_on_disk[group[j]] = append(placement.pgs_on_disk[group[j]], PGID(len(placement.Groups)))
	}

	placement.Groups = append(placement.Groups, group)
}

func (placement *DataPlacement) system_expand(added int) {
	placement.N = placement.N + added
	graph_new := make([][]int, placement.N)
	for i := 0; i < placement.N; i++ {
		graph_new[i] = make([]int, placement.N)
		if i < placement.N-added {
			for j := 0; j < placement.N-added; j++ {
				graph_new[i][j] = placement.recovery_load_graph[i][j]
			}
		}

	}
	placement.recovery_load_graph = graph_new
	for j := 0; j < added; j++ {
		placement.wv = append(placement.wv, 0)
		placement.pgs_on_disk = append(placement.pgs_on_disk, make([]PGID, 0))
		placement.new_added_node[placement.N-added+j] = 1
	}
}

func calc_std(arr []int) float64 {
	sum := 0.0
	for i := 0; i < len(arr); i++ {
		sum += float64(arr[i])
	}
	mean := sum / float64(len(arr))
	ret := 0.0
	for i := 0; i < len(arr); i++ {
		ret += (float64(arr[i]) - mean) * (float64(arr[i]) - mean)
	}
	ret /= float64(len(arr))
	return ret
}

func graph_to_arr(graph [][]int) []int {
	arr := make([]int, 0)
	for i := 0; i < len(graph); i++ {
		arr = append(arr, graph[i]...)
	}
	return arr
}

func (placement DataPlacement) calc_recovery_load_distribution_std() float64 {
	return calc_std(graph_to_arr(placement.recovery_load_graph))
}

func (placement DataPlacement) calc_data_distribution_std() float64 {
	lengths := make([]int, placement.N)
	for i, pgs := range placement.pgs_on_disk {
		lengths[i] = len(pgs)
	}
	return calc_std(lengths)
}

func greedy_find_next_placement_group(placements DataPlacement) PlacementGroup {

	var new_pg PlacementGroup = []int{}
	used := make(map[int]bool)

	//Used for System expansion control
	selected_new_added_disk := 0

	//Line 3 of Algorithm 1
	for j := 0; j < placements.n; j++ {

		minPGs := math.MaxInt32
		minLoad := math.MaxInt32
		minWV := math.MaxInt32

		for t := 0; t < placements.N; t++ {
			_, added_node := placements.new_added_node[t]
			if !used[t] && !added_node && len(placements.pgs_on_disk[t]) <= minPGs {
				minPGs = len(placements.pgs_on_disk[t])
			}
		}

		var chosen int

		for t := 0; t < placements.N; t++ {

			//Line 4 of Algorithm 1
			use, exist := used[t]
			if exist && use {
				continue
			}

			is_new_disk, _ := placements.new_added_node[t]
			//Used for System expansion control
			if selected_new_added_disk+is_new_disk > placements.c {
				continue
			}

			//Line 5 of Algorithm 1 is omitted, since there is no cabinet/server settings.

			//Line 6 of Algorithm 1

			if len(placements.pgs_on_disk[t]) > int(float64(minPGs)*(1+epsilon)) {
				continue
			}

			//When executing to obtain the first element of new_pg, the result is Line 1 of Algorithm.
			//Otherwise the result is Line 7 of the algorithm
			load := 0
			for m := 0; m < len(new_pg); m++ {
				load += placements.recovery_load_graph[t][new_pg[m]] + placements.get_element_for_repair_matrix(len(new_pg), m)
			}
			if load < minLoad || (load == minLoad && placements.wv[t] < minWV) {
				chosen = t
				minLoad = load
				minWV = placements.wv[t]
			}
		}

		used[chosen] = true
		new_pg = append(new_pg, chosen)

		if _, added := placements.new_added_node[chosen]; added {
			selected_new_added_disk++
		}

	}

	return new_pg

}

func random_find_next_placement_group(placements DataPlacement) PlacementGroup {

	var new_pg PlacementGroup = []int{}
	used := make(map[int]bool)

	for j := 0; j < placements.n; j++ {

		t := rand.Intn(placements.N)
		for {
			ok, exist := used[t]
			if !ok || !exist {
				break
			}
			t = rand.Intn(placements.N)
		}
		new_pg = append(new_pg, t)
		used[t] = true
	}

	return new_pg

}

func write_stds_to_file(std_a []float64, std_a_name string, std_b []float64, std_b_name string, filename string) {

	strides := 10
	file, _ := os.Create(filename)
	defer file.Close()

	file.WriteString(std_a_name + "," + std_b_name + "\n")

	for i := 0; i < len(std_a) || i < len(std_b); i += strides {
		x := 1.0
		y := 1.0
		if i < len(std_a) {
			x = std_a[i]
		}
		if i < len(std_b) {
			y = std_b[i]
		}
		file.WriteString(strconv.Itoa(i) + "," + strconv.FormatFloat(x, 'f', 3, 32) + "," + strconv.FormatFloat(y, 'f', 3, 32) + "\n")
	}
}

func get_data_and_recovery_load_stds(placement DataPlacement, nPG int, strategy Strategy) ([]float64, []float64) {
	data_std := []float64{}
	load_std := []float64{}
	for i := 0; i < nPG; i++ {
		var pg PlacementGroup
		if strategy == Greedy {
			pg = greedy_find_next_placement_group(placement)
		} else if strategy == Random {
			pg = random_find_next_placement_group(placement)
		}

		placement.add_group(pg)
		data_std = append(data_std, placement.calc_data_distribution_std())
		load_std = append(load_std, placement.calc_recovery_load_distribution_std())
	}
	return data_std, load_std
}

func get_recovery_load_stds_after_expansion(placement DataPlacement, nPG int, added int) []float64 {

	load_std := []float64{}
	for i := 0; i < nPG; i++ {
		var pg PlacementGroup
		pg = greedy_find_next_placement_group(placement)
		placement.add_group(pg)
		load_std = append(load_std, placement.calc_recovery_load_distribution_std())

		if i == nPG/2 {
			placement.system_expand(added)
		}

	}
	return load_std
}

func main() {
	N := 100
	k := 10
	n := 14
	code := RS

	placement_random := NewPlacement(N, code, n, k, 0, 1)
	placement_greedy := NewPlacement(N, code, n, k, 0, 1)

	random_data_std, random_load_std := get_data_and_recovery_load_stds(placement_random, N*10+1, Random)
	greedy_data_std, greedy_load_std := get_data_and_recovery_load_stds(placement_greedy, N*10+1, Greedy)

	write_stds_to_file(random_data_std, "random", greedy_data_std, "greedy", "Figure 3(a).csv")
	write_stds_to_file(random_load_std, "random", greedy_load_std, "greedy", "Figure 3(b).csv")

	greedy_expand_1_std := get_recovery_load_stds_after_expansion(NewPlacement(N, code, n, k, 0, 1), N*10+1, 1)
	greedy_expand_2_std := get_recovery_load_stds_after_expansion(NewPlacement(N, code, n, k, 0, 1), N*10+1, 2)

	write_stds_to_file(greedy_load_std, "greedy", greedy_expand_1_std, "greedy(expanded)", "Figure 4(a).csv")
	write_stds_to_file(greedy_load_std, "greedy", greedy_expand_2_std, "greedy(expanded)", "Figure 4(b).csv")
}
