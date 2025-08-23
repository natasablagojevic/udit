theory Vektori
imports Main

begin 

type_synonym vec3 = "int \<times> int \<times> int"

definition v1:: "vec3" where "v1 = (-1, 3, -1)"
definition v2:: "vec3" where "v2 = (1, 2, 5)"


fun add:: "vec3 \<Rightarrow> vec3 \<Rightarrow> vec3" 
  where "add (a1,b1,c1) (a2,b2,c2) = (a1+a2, b1+b2, c1+c2)"

fun sub:: "vec3 \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "sub (a1,b1,c1) (a2,b2,c2) = (a1-a2, b1-b2, c1-c2)"

fun mult:: "int \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "mult c (x,y,z) = (c*x, c*y, c*z)"

fun inter_product:: "vec3 \<Rightarrow> vec3 \<Rightarrow> int"
  where "inter_product (a1,b1,c1) (a2, b2, c2) = a1*a2 + b1*b2 + c1*c2"

value "add v1 v2 = (0,5,4)" 
value "sub v1 v2 = (-2,1,-6)"
value "mult 2 v1 = (-1,6,-2)"
value "inter_product v1 v2 = 0"

lemma "inter_product v v \<ge> 0"
  by (cases v) auto 

lemma "inter_product (add u v) w = inter_product u w + inter_product v w"
  by (cases u, cases v, cases w) (auto simp add: algebra_simps)

lemma "inter_product u (add v w) = inter_product u v + inter_product u w"
  by (cases u, cases v, cases w) (auto simp add: algebra_simps)

lemma "inter_product (mult c u) v = c * (inter_product u v)"
  by (cases u, cases v) (auto simp add: algebra_simps)

lemma "inter_product u (mult c v) = c * (inter_product u v)"
  by (cases u, cases v) (auto simp add: algebra_simps)

fun ortogonal:: "vec3 \<Rightarrow> vec3 \<Rightarrow> bool"
  where "ortogonal x y \<longleftrightarrow> (inter_product x y = 0)"

value "ortogonal v1 v2"

fun norm:: "vec3 \<Rightarrow> int" 
  where "norm (a,b,c) = a*a + b*b + c*c"

lemma 
  assumes "ortogonal u v"
  shows "norm (add u v) = norm u + norm v"
  using assms
  by (cases u, cases v) (auto simp add: algebra_simps)


end