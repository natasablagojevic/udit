theory Ispiti
  imports Main

begin

datatype tree = 
  List 
  | Cvor tree tree 

definition test_tree:: "tree" where "test_tree = Cvor (Cvor (Cvor List List) (Cvor (Cvor List List) (Cvor List List))) (Cvor (Cvor List List) (Cvor List List))"

fun tips:: "tree \<Rightarrow> nat"
  where "tips List = 1"
  | "tips (Cvor left right) = tips left + tips right"

value "tips test_tree"

fun height:: "tree \<Rightarrow> nat" 
  where "height List = 0"
  | "height (Cvor left right) =  1 + max (height left) (height right)"

fun complete_tree:: "nat \<Rightarrow> tree"
  where "complete_tree 0 = List"
  | "complete_tree (Suc n) = Cvor (complete_tree n) (complete_tree n)"

value "complete_tree 2"

value "size test_tree"

fun is_complete:: "(tree \<Rightarrow> 'a) \<Rightarrow> tree \<Rightarrow> bool"
  where "is_complete f List \<longleftrightarrow> True"
  | "is_complete f (Cvor left right) \<longleftrightarrow> (is_complete f left) \<and> (is_complete f right) \<and> (f left = f right)"

(*
lemma "is_complete height t = is_complete tips t"
  by (induction t) auto 

lemma "is_complete tips t = is_complete size t"
  by (induction t) auto

lemma "is_complete height t = is_complete size t"
  by (induction t) auto 
*)

(** -------------------------------------------------- **)

type_synonym vec3 = "int \<times> int \<times> int"


definition v1:: "vec3" where "v1 \<equiv> (-1,3,-1)"
definition v2:: "vec3" where "v2 = (1,2, 5)"

fun add:: "vec3 \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "add (x1, y1, z1) (x2, y2, z2) = (x1+x2, y1+y2, z1+z2)"

fun sub:: "vec3 \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "sub (x1, y1, z1) (x2, y2, z2) = (x1-x2, y1-y2, z1-z2)"

fun mult:: "int \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "mult c (x, y, z) = (c*x, c*y, c*z)"

fun inter_product:: "vec3 \<Rightarrow> vec3 \<Rightarrow> int"
  where "inter_product (x1, y1, z1) (x2, y2, z2) = x1*x2 + y1*y2 + z1*z2"

value "add v1 v2 = (0,5,4)"
value "sub v1 v2 = (-2,1,-6)"
value "mult 2 v1 = (-2,6,-2)"
value "inter_product v1 v2 = 0"

lemma "inter_product v v \<ge> 0"
  by (cases v) (auto simp add: algebra_simps)

lemma "inter_product (add u v) w = (inter_product u w) + (inter_product v w)"
  by (cases u, cases v, cases w) (auto simp add: algebra_simps)

lemma "inter_product u (add v w) = (inter_product u v) + (inter_product u w)"
  by (cases u, cases v, cases w) (auto simp add: algebra_simps)

lemma "inter_product (mult c u) v = c * (inter_product u v)"
  by (cases u, cases v) (auto simp add: algebra_simps)

lemma "inter_product u (mult c v) = c * (inter_product u v)"
  by (cases u, cases v) (auto simp add: algebra_simps)

fun orthogonal:: "vec3 \<Rightarrow> vec3 \<Rightarrow> bool"
  where "orthogonal u v \<longleftrightarrow> (inter_product u v = 0)"

fun norm:: "vec3 \<Rightarrow> int"
  where "norm (x, y, z) = x*x + y*y + z*z"

lemma 
  assumes "orthogonal u v"  
  shows "norm (add u v) \<le> (norm u) + (norm v)"
  using assms
  by (cases u, cases v) (auto simp add: algebra_simps)

(** -------------------------------------------------------------------------------------------- **)


datatype t3 = 
  List
  | Cvor t3 t3 t3 

fun br_cvor:: "t3 \<Rightarrow> nat"
  where "br_cvor List = 0"
  | "br_cvor (Cvor levo sredina desno) = 1 + br_cvor levo + br_cvor sredina + br_cvor desno"

fun br_list:: "t3 \<Rightarrow> nat"
  where "br_list List = 1" 
  | "br_list (Cvor l s d) = br_list l + br_list s + br_list d"

lemma "br_list t = 2 * br_cvor t + 1"
  by (induction t) auto

(** -------------------------------------------------------------------------------------------- **)


datatype integer =
  Zero ("\<zero>")
  | Pos nat 
  | Neg nat 

abbreviation PosOne:: integer ("+\<one>") where "+\<one> \<equiv> Pos 0"
abbreviation PosTwo:: integer ("+\<two>") where "+\<two> \<equiv> Pos 1"
abbreviation NegOne:: integer ("-\<one>") where "-\<one> \<equiv> Neg 0"
abbreviation NegTwo:: integer ("-\<two>") where "-\<two> \<equiv> Neg 1"

fun neg:: "integer \<Rightarrow> integer"
  where "neg Zero = Zero"
  | "neg (Pos n) = Neg n"
  | "neg (Neg n) = Pos n"

lemma "neg (neg n) = n" 
  by (induction n) auto 

fun succ:: "integer \<Rightarrow> integer"
  where "succ Zero = Pos 0"
  | "succ (Pos n) = Pos (Suc n)"
  | "succ (Neg 0) = Zero "
  | "succ (Neg (Suc n)) = Neg n"

fun pred:: "integer \<Rightarrow> integer"
  where "pred Zero = Neg 0"
  | "pred (Pos 0) = Zero"
  | "pred (Pos (Suc n)) = Pos n"
  | "pred (Neg n) = Neg (Suc n)"

fun leq:: "nat \<Rightarrow> nat \<Rightarrow> bool" (infixl "\<sqsubseteq>" 100)
  where "leq x y \<longleftrightarrow> x \<le> y"

lemma refleksivnost:
  "\<forall>x. x \<sqsubseteq> x"
  by auto 

lemma antisimetricnost:
  "\<forall>x y. x \<sqsubseteq> y \<and> y \<sqsubseteq> x \<longrightarrow> x = y"
  by auto 

lemma tranzitivnost:
  "\<forall>x y z. x \<sqsubseteq> y \<and> y \<sqsubseteq> z \<longrightarrow> x \<sqsubseteq> z"
  by auto 


end