theory F1
  imports Main HOL.Real

begin 

lemma "P \<and> Q \<longrightarrow> P \<or> Q"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
  done

lemma "P \<and> Q \<longrightarrow> P \<or> Q"
proof
  assume "P \<and> Q"
  then have "P" "Q" by auto
  from \<open>Q\<close> show "P \<or> Q" by auto
qed

lemma "\<not>(A \<or> B) \<longleftrightarrow> \<not> A \<and> \<not> B"
proof
  assume *:"\<not> (A \<or> B)"
  show "\<not> A \<and> \<not> B"
  proof
    show "\<not> A"
    proof
      assume "A"
      from this have "A \<or> B" by auto 
      from \<open>A \<or> B\<close> \<open>\<not>(A \<or> B)\<close> show False by auto 
    qed
  next
    show "\<not> B"
    proof
      assume "B"
      from this have "A \<or> B" by auto
      from \<open>A \<or> B\<close> \<open>\<not>(A \<or> B)\<close> show False by auto
    qed
  qed

next 
  assume "\<not> A \<and> \<not> B"
  then have "\<not> A" "\<not> B" by auto
  show "\<not> (A \<or> B)"
  proof
    assume "A \<or> B"
    then show False 
    proof
      assume "A"
      with \<open>\<not> A\<close> show False by auto       
    next
      assume "B"
      with \<open>\<not>B\<close> show False by auto
    qed
  qed
qed

lemma lemma "\<not>(A \<and> B) \<longleftrightarrow> \<not> A \<or> \<not> B" (is "?l \<longleftrightarrow> ?d")
proof
  assume "\<not> (A \<and> B)"
  show " \<not> A \<or> \<not> B"
  proof (rule ccontr)
    assume "\<not> (\<not> A \<or> \<not> B)"
    have "A \<and> B" 
    proof
      show "A"
      proof (rule ccontr)
        assume "\<not>A"
        then have "\<not> A \<or> \<not> B" by auto
        from this \<open>\<not>(\<not> A \<or> \<not> B)\<close>  show False by auto
      qed
    next
      show "B"
      proof (rule ccontr)
        assume "\<not> B"
        then have "\<not> A \<or> \<not> B" by auto 
        from this \<open>\<not>(\<not> A \<or> \<not> B)\<close> show False by auto
      qed
    qed
    with \<open>\<not>(A \<and> B)\<close> show False by auto
  qed

next 
  assume "\<not> A \<or> \<not> B"
  show "\<not> (A \<and> B)"
    sorry
qed


lemma "(\<forall>x y. R x y \<longrightarrow> R y x) \<and> (\<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z) \<and> (\<forall>x. \<exists>y. R x y) \<longrightarrow> (\<forall>x. R x x)"
  sorry

lemma 
  assumes "inj f"
  shows "f ` (A \<inter> B) = f ` A \<inter> f ` B"
proof 
  show "f ` (A \<inter> B) \<subseteq> f ` A \<inter> f ` B"
  proof
    fix y
    assume "y \<in> f ` (A \<inter> B)"
    then obtain x where "x \<in> A \<inter> B" "f x = y" by auto 
    then have  "x \<in> A" "x \<in> B" by auto 
    then have "y \<in> f ` A" "y \<in> f ` B" using \<open>f x = y\<close>  by auto
    then show "y \<in> f ` A \<inter> f ` B" by auto
  qed

next 
  show "f ` A \<inter> f ` B \<subseteq> f ` (A \<inter> B)"
  proof
    fix y
    assume "y \<in> f ` A \<inter> f ` B" 
    then have "y \<in> f ` A" "y \<in> f ` B" by auto 
    from \<open>y \<in> f ` A\<close> obtain x1 where "x1 \<in> A" "f x1 = y" by auto
    from \<open>y \<in> f ` B\<close> obtain x2 where "x2 \<in> B" "f x2 = y" by auto 
    have "f x1 = f x2" using \<open>f x1 = y\<close> \<open>f x2 = y\<close> by auto 
    then have "x1 = x2" using \<open>inj f\<close> unfolding inj_def  by auto 
    then have "x1 \<in> A" "x1 \<in> B" using \<open>x1 \<in> A\<close> \<open>x2 \<in> B\<close> by auto
    then have "x1 \<in> A \<inter> B" by auto
    then have "f x1 \<in> f ` (A \<inter> B)" by auto
    then show "y \<in> f ` ( A \<inter> B)" using \<open>f x1 = y\<close> by auto
  qed
qed

(* --------- BROOJEVI ------------*)

term "3::nat"
term "3::rat"

(* div - celobrojno deljenje
   mod - ostatak pri deljenju

  obratiti paznju na oduzimanje na prirodnim brojevima

 nat: +,*,div, mod
 int, real: +,-,/
*)

(*
  x * (y + z) = x * y + x * z

  polja, grupe, prsteni
*)


find_theorems "(_::nat) * (_ + _) = _ * _ + _ * _"

thm algebra_simps 
thm field_simps (* deljenje *)

 (* by simp add: algebra_simps *)

thm power2_eq_square

lemma 
  fixes x y :: real
  shows "(x - y) * (x + y) = x^2 - y^2"
  (*using [[show_types]]*)
proof -
  have "(x - y) * (x + y) = (x - y) * x + (x - y) * y" by (rule distrib_left) 
  also have "... = (x * x - y * x) + (x - y) * y" by (subst left_diff_distrib, rule refl)
  also have "... = (x * x - y * x) + (x * y - y * y)" by (subst left_diff_distrib, rule refl)
  also have "... = (x * x - y * x + x * y) - y * y" by (rule add_diff_eq)
  also have "... = (x * x - x * y + x * y) - y * y" by (subst mult.commute[of y x], rule refl)
  also have "... = x * x - y * y" by (subst diff_add_cancel, rule refl)
  finally show ?thesis by (subst power2_eq_square)+
qed








end