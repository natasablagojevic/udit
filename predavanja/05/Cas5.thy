theory Cas5
  imports Main

begin

(*
zbir :: real \<Rightarrow> (real \<Rightarrow> real)

karijevanje

zbir(2, 3) = 5

(zbir 2) 3 

(zbir 2) x = 2 + x 

(\<lambda> x y. x + y)

*)


term inj

thm inj_def

term surj
thm surj_def

term inj_on 

term bij

term comp 
thm comp_def

lemma 
  fixes f :: "'a \<Rightarrow> 'b"
  fixes g :: "'c \<Rightarrow> 'a"
  assumes "inj f" "inj g"
  shows "inj (f \<circ> g)"
proof
  fix x y :: "'c" 
  assume "(f \<circ> g) x = (f \<circ> g) y"

  then have "f (g x) = f (g y)"
    by (auto simp add: comp_def)
    (*unfolding comp_def 
    by auto*) 

  then have "g x = g y"
    using \<open>inj f\<close>
    unfolding inj_def
    by auto 
 (* by (auto simp add: inj_def) *)

  then show "x = y"
    using \<open>inj g\<close>
    unfolding inj_def
    by auto 
qed


lemma 
  assumes "surj f" "surj g"
  shows "surj (f \<circ> g)"
  unfolding surj_def
proof
  fix y

  from \<open>surj f\<close> obtain a where "f a = y"
    unfolding surj_def
    by metis

  moreover

  from \<open>surj g\<close> obtain x where "g x = a"
    unfolding surj_def 
    by metis 

  ultimately

  have "f (g x) = y"
    (*using \<open>g x = a\<close>   \<open>f a = y\<close>*)
    by auto
(*
  have "\<exists> x. y = f (g x)"
    sorry 
*)

  then show "\<exists> x. y = (f \<circ> g) x"
    by auto
qed

term "f ` A"
term "f -` B"

(*moze biti na kolokvijumu*)

lemma 
  assumes "inj f"
  shows "f -` (f ` A) = A"
proof 
  show " f -` f ` A \<subseteq> A"
  proof 
    fix x 
    assume "x \<in> f -` (f ` A)"

    then have "f x \<in> f ` A"
      by auto

    then obtain x' where "f x' = f x" "x' \<in> A"
      by auto 

    then show "x \<in> A"
      using \<open>inj f\<close>
      unfolding inj_def 
      by auto
  qed 

next
  show " A \<subseteq> f -` f ` A"
  proof 
    fix x 
    assume "x \<in> A"

    then have "f x \<in> f ` A"
      by auto  

    then show "x \<in> f -` (f ` A)"
      by auto  

  qed 
qed 

lemma 
  "f -` (f ` A \<inter> B) \<supseteq> A \<inter> f -` B"
proof
  fix x 
  assume "x \<in> A \<inter> f -` B"

  then have "x \<in> A" "f x \<in> B"
    by auto 

  moreover 

  have "f x \<in> f ` A"
    using \<open>x \<in> A\<close>
    by auto 

  have "f x \<in> f ` A \<inter> B"
    using \<open>f x \<in> f ` A\<close> \<open>f x \<in> B\<close>
    by auto 

    then show "x \<in> f -` (f ` A \<inter> B)"
      by auto
  qed 


  term Pow 

definition partitivni :: "'a set \<Rightarrow> 'a set set" where
  "partitivni A = {X. X \<subseteq> A}"


(*"\<not> (\<exists> f. bij_betw f A (artitivni A))"*)
lemma 
  "\<not> bij_betw f A (partitivni A)"
proof
  assume "bij_betw f A (partitvni A)"

  let ?S = "{x \<in> A. x \<notin> f x}"

  have "?S \<subseteq> A"
    by auto 

  then have "?S \<in> partitivni A"
    unfolding partitivni_def
    by auto 

  then obtain x where "x \<in> A" "f x = ?S"
    using \<open>bij_betw f A (partitivni A)\<close>
    sledgehammer


  show False
  proof (cases "x \<in> f x")

    case True 
    then have "x \<in> ?S" 
      using \<open>f x = ?S\<close>
      by metis 

    then have "x \<notin> f x"
      by auto 

    then show False
      using \<open>x \<in> f x\<close>
      by auto 

  qed

next 
  case False 
  then have "x \<in> ?S"
    using \<open>x \<in> A\<close>
    by auto 

  then have "x \<in> f x"
    using \<open>f x = ?S\<close>
    by metis 

  with \<open>x \<notin> f x\<close> show False
    by auto 

qed

end 