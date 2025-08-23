theory Jan
  imports Main

begin 

datatype tree = 
  List 
  | Cvor tree tree

definition test_inst:: "tree" where "test_inst = Cvor (Cvor (Cvor (List) (List)) (Cvor (Cvor List List) (Cvor List List))) (Cvor (Cvor List List) (Cvor List List))"

fun tips:: "tree \<Rightarrow> nat" 
  where "tips List = 1"
  | "tips (Cvor levo desno) = tips levo + tips desno"

fun heigh:: "tree \<Rightarrow> nat" 
  where "heigh List = 0"
  | "heigh (Cvor levo desno) = 1 + max (heigh levo) (heigh desno)"

value "tips test_inst"
value "heigh test_inst"

fun complete_tree:: "nat \<Rightarrow> tree"
  where "complete_tree 0 = List"
  | "complete_tree (Suc n) = Cvor (complete_tree n) (complete_tree n)"

value "complete_tree 3"

fun is_complete:: "(tree \<Rightarrow> 'a) \<Rightarrow> tree \<Rightarrow> bool"
  where "is_complete f List \<longleftrightarrow> True"
  | "is_complete f (Cvor levo desno) \<longleftrightarrow> (is_complete f levo) \<and> (is_complete f desno) \<and> (f levo = f desno)"

lemma tips_complete_tree[simp]: "tips (complete_tree n) = 2^n"
  by (induction n) simp_all

lemma height_complete_tree[simp]: "heigh (complete_tree n) = n"
  by (induction n) (simp_all)

lemma pow2_inj_nat: "(2::nat)^m = 2^n \<Longrightarrow> m = n"
  by (simp add: power_inject_exp)

lemma tips_eq__pow_height:
  assumes "is_complete heigh t"
  shows "tips t = 2^(heigh t)"
  using assms
  by (induction t) (auto simp add: algebra_simps)

lemma eq_height_iff_eq_tips_on_complete:
  assumes "is_complete heigh l" "is_complete heigh r"
  shows "heigh l = heigh r \<longleftrightarrow> tips l = tips r"
proof
  assume "heigh l = heigh r"
  with tips_eq__pow_height[OF assms(1)] tips_eq__pow_height[OF assms(2)]
  show "tips l = tips r" by simp
    
next 
  assume "tips l = tips r"
  with tips_eq__pow_height[OF assms(1)] tips_eq__pow_height[OF assms(2)]
  have "2^(heigh l) = 2^(heigh r)" by simp
  then show "heigh l = heigh r" by (rule pow2_inj_nat)
qed

lemma "is_complete heigh t = is_complete tips t"
proof (induction t)
  case List
  then show ?case by simp
next
  case (Cvor l r)
  note IHl = Cvor.IH(1) and IHr = Cvor.IH(2) 
  have X: "is_complete tips l \<and> is_complete tips r \<Longrightarrow> (heigh l = heigh r \<longleftrightarrow> tips l = tips r)"
  proof - 
    assume "is_complete tips l \<and> is_complete tips r"
    hence "is_complete heigh l \<and> is_complete heigh r" using IHl IHr by simp
    then show ?thesis by (auto intro!: eq_height_iff_eq_tips_on_complete)
  qed
  then show ?case using IHl IHr X by simp
qed

lemma "is_complete heigh t = is_complete tips t"
  by (induction t) auto 

lemma "is_complete tips t = is_complete size t"
  by (induction t) auto 

lemma "is_complete heigh t = is_complete size t"
  by (induction t) (auto simp add: algebra_simps)


end