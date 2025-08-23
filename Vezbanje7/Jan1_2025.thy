theory Jan1_2025
  imports Main

begin


datatype t3 = 
  List
  | Cvor t3 t3 t3 


fun br_cvor:: "t3 \<Rightarrow> nat"
  where "br_cvor List = 0"
  | "br_cvor (Cvor l m r) = 1 + br_cvor l + br_cvor m + br_cvor r"


fun br_list:: "t3 \<Rightarrow> nat"
  where "br_list List = 1"
  | "br_list (Cvor l m r) = br_list l + br_list m + br_list r"

(*
lemma "\<exists>a b. \<forall>t. br_list t = a * br_cvor t + b"
  by (induction t) (auto)
*)

lemma "br_list t = 2 * br_cvor t + 1"
  by (induction t) (auto)

(** ------ SEP1 ------  **)

(** ---- vektori -----**)

type_synonym vec3 = "int \<times> int \<times> int"

definition v1:: "vec3" where "v1 \<equiv> (-1,3,-1)"
definition v2:: "vec3" where "v2 \<equiv> (1,2,5)"


fun add:: "vec3 \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "add (a1,b1,c1) (a2,b2,c2) = (a1+a2, b1+b2, c1+c2)"

fun sub:: "vec3 \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "sub (a1,b1,c1) (a2,b2,c2) = (a1-a2, b1-b2, c1-c2)"

fun mult:: "int \<Rightarrow> vec3 \<Rightarrow> vec3" 
  where "mult x (a,b,c) = (x*a, x*b, x*c)"

fun inter_product:: "vec3 \<Rightarrow> vec3 \<Rightarrow> int"
  where "inter_product (a1,b1,c1) (a2,b2,c2) = a1*a2 + b1*b2 + c1*c2"

value "add v1 v2 = (0,5,4)"
value "sub v1 v2 = (-2,1,-6)"
value "mult 2 v1 = (-2,6,-2)"
value "inter_product v1 v2 = 0"

lemma "inter_product v1 v1 \<ge> 0"
  unfolding v1_def 
  by auto 

lemma "inter_product v v \<ge> 0"
proof (cases v)
  fix a b c
  assume "v = (a, b, c)"
  then show "inter_product v v \<ge> 0"
    by auto
qed

lemma "inter_product (add u v) w = inter_product u w + inter_product v w"
  by (cases u, cases v, cases w) (auto simp add: algebra_simps)

lemma "inter_product (mult c u) w = c * (inter_product u w)"
  by  (cases u, cases w) (auto simp add: algebra_simps)

lemma "inter_product u (add v w) = inter_product u v + inter_product u w"
  by (cases u, cases v, cases w) (auto simp add: algebra_simps)

lemma "inter_product u (mult c v) = c * (inter_product u v)"
  by (cases u, cases v) (auto simp add: algebra_simps)


fun kv_norma:: "vec3 \<Rightarrow> int"
  where "kv_norma (a,b,c) = a*a + b*b + c*c"

fun ortogonal:: "vec3 \<Rightarrow> vec3 \<Rightarrow> bool"
  where "ortogonal x y \<longleftrightarrow> inter_product x y = 0"

lemma pitagora:
  assumes "ortogonal u v"
  shows "kv_norma (add u v) = kv_norma u  + kv_norma v"
  using assms
  by (cases u, cases v)  (auto simp add: algebra_simps)

(** ----- BINARNO STABLO -----  **)

datatype 'a tree  = 
  List 
  | Cvor "'a tree" 'a "'a tree"

(*definition tree_test:: "'a tree" where "tree_test \<equiv> Cvor (Cvor (Cvor List 1 List) 5 (Cvor (Cvor List 2 List) 3 (Cvor List 4 List))) 6 (Cvor (Cvor List 7 List) 8 (Cvor List 9 List))" 
*)

definition tree_test:: "nat tree" where "tree_test \<equiv> Cvor (Cvor (Cvor List 1 List) 5 (Cvor (Cvor List 2 List) 3 (Cvor List 4 List))) 6 (Cvor (Cvor List 7 List) 8 (Cvor List 9 List))"


definition test_drvo:: "nat tree" where 
  "test_drvo \<equiv> Cvor (Cvor List 1 List) 3 (Cvor (Cvor List 4 List) 2 (Cvor List 3 List))"

fun zbir:: "nat tree \<Rightarrow> nat"
  where "zbir List = 0"
  | "zbir (Cvor levo x desno) = x + zbir levo + zbir desno"

value "zbir test_drvo"
value "zbir tree_test"

fun tips:: "nat tree \<Rightarrow> nat"
  where "tips List = 0"
  | "tips (Cvor List _ List) = 1"
  | "tips (Cvor levo x desno) =  tips levo + tips desno"

value "tips test_drvo"
value "tips tree_test"


fun broj_cvorova:: "nat tree \<Rightarrow> nat"
  where "broj_cvorova List = 0"
  | "broj_cvorova (Cvor levo x desno) = 1 + broj_cvorova levo + broj_cvorova desno "

value "broj_cvorova test_drvo"
value "broj_cvorova tree_test"

fun broj_unutrasnjih_cvorova:: "nat tree \<Rightarrow> nat"
  where "broj_unutrasnjih_cvorova List = 0"
  | "broj_unutrasnjih_cvorova (Cvor List _ List) = 0"
  | "broj_unutrasnjih_cvorova (Cvor levo x desno) = 1 + broj_unutrasnjih_cvorova levo + broj_unutrasnjih_cvorova desno"

value "broj_unutrasnjih_cvorova tree_test"

fun visina:: "nat tree \<Rightarrow> nat"
  where "visina List = 0"
  | "visina (Cvor levo x desno) = 1 + (if visina levo > visina desno then visina levo else visina desno)"

fun visina_alt:: "nat tree \<Rightarrow> nat"
  where "visina_alt List = 0"
  | "visina_alt (Cvor levo x desno) = 1 + max (visina_alt levo) (visina_alt desno)"

value "visina tree_test"
value "visina_alt tree_test"

fun najveci_element:: "nat tree \<Rightarrow> nat"
  where "najveci_element List = 0"
  | "najveci_element (Cvor levo x List) = x"
  | "najveci_element (Cvor levo x desno) = najveci_element desno"

value "najveci_element tree_test"
value "najveci_element test_drvo"

fun najmanji_element:: "nat tree \<Rightarrow> nat"
  where "najmanji_element List = 0"
  | "najmanji_element (Cvor List x desno) = x"
  | "najmanji_element (Cvor levo x desno) = najmanji_element levo"

value "najmanji_element tree_test"
value "najmanji_element test_drvo"


fun pretrazi_stablo:: "nat tree \<Rightarrow> nat \<Rightarrow> bool"
  where "pretrazi_stablo List br \<longleftrightarrow>False"
  | "pretrazi_stablo (Cvor levo x desno) br \<longleftrightarrow>  (pretrazi_stablo levo br) \<or> (x = br) \<or> (pretrazi_stablo desno br)"


value "pretrazi_stablo test_tree 11"

fun savrseno:: "nat tree \<Rightarrow> bool"
  where "savrseno List = True "
  | "savrseno (Cvor levo x desno) = (savrseno levo \<and> savrseno desno \<and> visina levo = visina desno)"

(*
fun complete:: "nat tree \<Rightarrow> nat"
  where "complete List \<longleftrightarrow> True"
  | "complete (Cvor levo x desno) \<longleftrightarrow> (savrseno l \<and> complete desno \<and> visina levo = visina desno) \<or> (complete levo \<and> savrseno desno \<and> visina levo = Suc (visina desno))"
 *)

fun complete_tree:: "nat \<Rightarrow> nat \<Rightarrow> nat tree" 
  where "complete_tree 0 x = List" 
  | "complete_tree (Suc n) x = Cvor (complete_tree ((n+1) div 2) x) x (complete_tree (n div 2) x)"

value "complete_tree 5 1" 

fun infiks:: "'a tree \<Rightarrow> 'a list"
  where "infiks List = []"
  | "infiks (Cvor levo x desno) = infiks levo @ [x] @ infiks desno"

value "infiks tree_test"

fun prefiksno:: "'a tree \<Rightarrow> 'a list"
  where "prefiksno List = []"
  |  "prefiksno (Cvor levo x desno) = [x] @ prefiksno levo @ prefiksno desno"

value "prefiksno tree_test"


fun postfiksno:: "'a tree \<Rightarrow> 'a list"
  where "postfiksno List = []"
  | "postfiksno (Cvor levo x desno) = postfiksno levo @ postfiksno desno @ [x]"

value "postfiksno tree_test"

datatype drvot = 
  List 
  | Cvor drvot drvot

fun kompletno:: "nat \<Rightarrow> drvot"
  where "kompletno 0 = List"
  | "kompletno (Suc n) = Cvor (kompletno n) (kompletno n)"

value "kompletno 2"

end

