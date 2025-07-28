theory drvo
  imports Main "HOL-Library.Multiset"

begin

datatype 'a drvo = List
  | Cvor "'a drvo" 'a "'a drvo"

primrec zbir:: "nat drvo \<Rightarrow> nat"
  where "zbir List = 0"
  | "zbir (Cvor lt x rt) = zbir lt + x + zbir rt"

definition test_drvo:: "nat drvo"
  where "test_drvo \<equiv> Cvor (Cvor List 1 List) 3 (Cvor (Cvor List 4 List) 2 (Cvor List 3 List))"

value "zbir test_drvo"

primrec sadrzi:: "'a drvo \<Rightarrow> 'a \<Rightarrow> bool"
  where "sadrzi List a \<longleftrightarrow> False"
  | "sadrzi (Cvor ls x rt) a \<longleftrightarrow> (sadrzi ls a) \<or> (x = a) \<or> (sadrzi rt a)"

value "sadrzi test_drvo 4"

fun skup:: "'a drvo \<Rightarrow> 'a set"
  where "skup List = {}"
  | "skup (Cvor levo x desno) = (skup levo) \<union> {x} \<union> (skup desno)"

value "skup test_drvo"

lemma priprada_skup_sadrzi:
  shows "a \<in> skup d \<longleftrightarrow> sadrzi d a"
  by (induction d) auto 

primrec infiks:: "'a drvo \<Rightarrow> 'a list" 
  where "infiks List = []"
  | "infiks (Cvor levo x desno) = (infiks levo) @ [x] @ (infiks desno)"

value "infiks test_drvo"

primrec prefiks:: "'a drvo \<Rightarrow> 'a list"
  where "prefiks List = []"
  | "prefiks (Cvor levo x desno) = [x] @ (prefiks levo) @ (prefiks desno)"

primrec postfiks:: "'a drvo \<Rightarrow> 'a list"
  where "postfiks List = []"
  | "postfiks (Cvor levo x desno) = (postfiks levo) @ (postfiks desno) @ [x]"

lemma set_iniks_skup[simp]:
  shows "set (infiks d) = skup d"
  by (induction d) auto

primrec multiskup:: "'a drvo \<Rightarrow> 'a multiset" 
  where "multiskup List = {#}"
  | "multiskup (Cvor levo x desno) = multiskup levo + {#x#} + multiskup desno"

lemma mset_infiks_multiskup[simp]:
  shows "mset (infiks d) = multiskup d"
  by (induction d) auto

primrec infiks_opt' :: "'a drvo \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "infiks_opt' List xs = xs"
  | "infiks_opt' (Cvor levo x desno) xs = infiks_opt' levo (x # infiks_opt' desno xs)"

definition infiks_opt:: "'a drvo \<Rightarrow> 'a list" 
  where "infiks_opt xs = infiks_opt' xs []"

value "infiks_opt test_drvo"

lemma infiks_opt'_append:
  shows "infiks_opt' d xs@ys = infiks_opt' d (xs@ys)"
  by (induction d arbitrary: xs) auto

lemma infiks_infiks_opt:
  shows "infiks d = infiks_opt d"
  unfolding infiks_opt_def 
  by (induction d) (auto simp add: infiks_opt'_append)

primrec sortirano:: "('a::linorder) drvo \<Rightarrow> bool"
  where "sortirano List \<longleftrightarrow> True"
  | "sortirano (Cvor levo x desno) \<longleftrightarrow> (\<forall> a \<in> skup levo. a \<le> x) 
      \<and> (\<forall> a \<in> skup desno. a \<ge> x) 
      \<and> (sortirano levo) \<and> (sortirano desno)"

value "infiks test_drvo"
value "sortirano test_drvo"

definition test_drvo_sortirano:: "nat drvo"
  where "test_drvo_sortirano \<equiv> Cvor (Cvor List 1 (Cvor List 2 List)) 3 (Cvor (Cvor List 3 List) 4 List)"

value "infiks test_drvo_sortirano"
value "sortirano test_drvo_sortirano"

lemma sortirano_sorted_infiks:
  shows "sortirano d \<Longrightarrow> sorted (infiks d)"
  by (induction d) (auto simp add: sorted_append order_trans)

primrec ubaci:: "('a::linorder) \<Rightarrow> 'a drvo \<Rightarrow> 'a drvo"
  where "ubaci a List = (Cvor List a List)"
  | "ubaci a (Cvor levo x desno) = (if a \<le> x then (Cvor (ubaci a levo) x desno) else (Cvor levo x (ubaci a desno)))"

lemma sadrzi_ubaci[simp]:
  shows "sadrzi (ubaci x d) x"
  by (induction d) auto

lemma skup_ubaci[simp]:
  shows "skup (ubaci x d) = {x} \<union> skup d"
  by (induction d) auto 

lemma multiskup_ubaci[simp]:
  shows "multiskup (ubaci x d) = {#x#} + multiskup d"
  by (induction d) auto

lemma zbir_ubaci[simp]:
  shows "zbir (ubaci x d) = x + zbir d"
  by (induction d) auto 

lemma sortirano_ubaci[simp]:
  shows "sortirano d \<Longrightarrow> sortirano (ubaci x d)"
  by (induction d) auto 

primrec listaUDrvo :: "('a::linorder) list \<Rightarrow> 'a drvo"
  where "listaUDrvo [] = List"
  | "listaUDrvo (x#xs) = ubaci x (listaUDrvo xs)"

lemma [simp]: "skup (listaUDrvo xs) = set xs"
  by (induction xs) auto 

lemma [simp]: "multiskup (listaUDrvo xs) = mset xs"
  by (induction xs) auto 

lemma [simp]: "sortirano (listaUDrvo x)"
  by (induction x) auto 

definition sortiraj:: "nat list \<Rightarrow> nat list"
  where "sortiraj xs = infiks (listaUDrvo xs)"

theorem "sorted (sortiraj xs)"
  unfolding sortiraj_def 
  by (induction xs) (auto simp add: sortirano_sorted_infiks)

theorem "set (sortiraj xs) = set xs"
  unfolding sortiraj_def 
  by (induction xs) auto 

theorem "mset (sortiraj xs) = mset xs"
  unfolding sortiraj_def 
  by (induction xs) auto 


end