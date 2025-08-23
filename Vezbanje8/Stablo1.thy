theory Stablo1
  imports Main

begin 

datatype 'a drvo = 
  List 
  | Cvor "'a drvo" 'a "'a drvo"


definition test:: "nat drvo" where "test = Cvor (Cvor (Cvor List 3 List) 7 (Cvor (Cvor List 8 List) 10 (Cvor List 12 List))) 15 (Cvor (Cvor List 20 List) 25 (Cvor List 30 List))"

fun visina:: "nat drvo \<Rightarrow> nat"
  where "visina List = 0"
  | "visina (Cvor left x right) = 1 + max (visina left) (visina right)"

value "visina test"

fun find:: "nat drvo \<Rightarrow> nat \<Rightarrow> bool" 
  where "find List a \<longleftrightarrow> False"
  | "find (Cvor left x right) a \<longleftrightarrow> (find left a) \<or> (find right a) \<or> (x = a)"

value "find test 89"

fun max_element:: "nat drvo \<Rightarrow> nat"
  where "max_element List = 0"
  | "max_element (Cvor List x List) = x"
  | "max_element (Cvor left x right) = max_element right"

value "max_element test"

fun min_element:: "nat drvo \<Rightarrow> nat"
  where "min_element List = 0"
  | "min_element (Cvor List x List) = x"
  | "min_element (Cvor left x right) = min_element left"

value "min_element test"

fun num_nodes:: "nat drvo \<Rightarrow> nat" 
  where "num_nodes List = 0"
  | "num_nodes (Cvor left x right) = 1 + num_nodes left + num_nodes right"


value "num_nodes test"

fun num_inner_nodes:: "nat drvo \<Rightarrow> nat"
  where "num_inner_nodes List = 0"
  | "num_inner_nodes (Cvor List x List) = 0"
  | "num_inner_nodes (Cvor left x right) = 1 + num_inner_nodes left + num_inner_nodes right"


value "num_inner_nodes test"

fun num_leafs:: "nat drvo \<Rightarrow> nat"
  where "num_leafs List = 1"
  | "num_leafs (Cvor left x right) = num_leafs left + num_leafs right"

value "num_leafes test"

fun num_real_leafs:: "nat drvo \<Rightarrow> nat"
  where "num_real_leafs List = 1"
  | "num_real_leafs (Cvor List x List) = 1"
  | "num_real_leafs (Cvor left x right) = num_real_leafs left + num_real_leafs right"

value "num_real_leafs test"

fun elems_on_ith_level:: "nat drvo \<Rightarrow> nat \<Rightarrow> nat list" 
  where "elems_on_ith_level List _ = []"
  | "elems_on_ith_level (Cvor left x right) 0 = [x]"
  | "elems_on_ith_level (Cvor left x right) (Suc i) = elems_on_ith_level left i @ elems_on_ith_level right i"

value "elems_on_ith_level test 2"

fun num_on_ith_level:: "nat drvo \<Rightarrow> nat \<Rightarrow> nat" 
  where "num_on_ith_level List _ = 0"
  | "num_on_ith_level (Cvor left x right) 0 = 1"
  | "num_on_ith_level (Cvor left x right) (Suc i) = num_on_ith_level left i + num_on_ith_level right i"

value "num_on_ith_level test 2"

fun sum:: "nat drvo \<Rightarrow> nat"
  where "sum List = 0" 
  | "sum (Cvor left x right) = x + sum left + sum right"

value "sum test"

fun print_leaf_nodes:: "nat drvo \<Rightarrow> nat list"
  where "print_leaf_nodes List = []"
  | "print_leaf_nodes (Cvor List x List) = [x]"
  | "print_leaf_nodes (Cvor left x right) = print_leaf_nodes left @ print_leaf_nodes right"

value "print_leaf_nodes test"

fun print_inner_nodes:: "nat drvo \<Rightarrow> nat list"
  where "print_inner_nodes List = []"
  | "print_inner_nodes (Cvor List x List) = []"
  | "print_inner_nodes (Cvor left x right) = print_inner_nodes left @ [x]  @ print_inner_nodes right"


value "print_inner_nodes test"

fun add_node:: "nat drvo \<Rightarrow> nat \<Rightarrow> nat drvo "
  where "add_node List a = Cvor List a List"
  | "add_node (Cvor left x right) a = (if a \<le> x then (Cvor (add_node left a) x right) else (Cvor left x (add_node right a)))"

value "add_node test 1"









end