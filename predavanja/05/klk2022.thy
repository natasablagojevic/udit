theory Kolokvijum2022_resenja
imports Main
begin

(* Napomena: 
- Dokazi moraju biti detaljni. Nije dozvoljeno koriscenje sledgehammer-a.
- Prvi zadatak se reЕЎava uz pomoД‡ apply-skript dokaza. 
- Za ostale zadatke treba navesti detaljan Isar dokaz (korak po korak) *)

text \<open>1. Dokazati koriЕЎД‡enjem pravila prirodne dedukcije za klasiДЌnu logiku prvog reda naredne leme.\<close>

(* a *)
(* 4 poena *)
lemma "(\<not> A \<longrightarrow> B) \<and> (\<not> A \<longrightarrow> \<not> B) \<longrightarrow> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  back
  apply assumption
  done

(* b *)
(* 6 poena *)
lemma "((\<exists> x. P x) \<longleftrightarrow> (\<exists> x. Q x)) \<and> (\<forall> x y. P x \<and> Q y \<longrightarrow> (R x \<longleftrightarrow> S y)) \<longrightarrow>
       ((\<forall> x. P x \<longrightarrow> R x) \<longrightarrow> (\<forall> x. Q x \<longrightarrow> S x))"
  apply (rule impI)
  apply (erule conjE)
   apply (rule impI)
  apply (rule allI)
  apply (rule impI)
   apply (erule iffE)
   apply (erule impE)    (* 30 % resenja - 2 poena *)
    back
    apply (rule_tac x=x in exI)
    apply assumption
   apply (erule exE)
   apply (erule_tac x=xa in allE)
   apply (erule_tac x=x in allE)
   apply (erule impE)
    back
    apply (rule conjI)
     apply assumption
    apply assumption
   apply (erule_tac x=xa in allE)
   apply (erule impE)
    back
    apply assumption
   apply (erule iffE)
   apply (erule_tac impE)
    back
    apply assumption
   apply assumption
  done

text \<open>2. Zapisati dokaz naredne skupovne formule u jeziku Isar\<close>

(* skupovi *)
(* 5 poena *)
lemma "(A - B) \<union> (B - A) \<subseteq> (A \<union> B) - (B \<inter> A)"
  proof
    fix x
    assume "x \<in> (A - B) \<union> (B - A)"
    then show "x \<in> (A \<union> B) - (B \<inter> A)"
    proof
      assume "x \<in> A - B"
      then have "x \<in> A" "x \<notin> B"
        by auto
      from `x \<in> A` have "x \<in> A \<union> B"
        by auto
      moreover
      from `x \<notin> B` have "x \<notin> A \<inter> B"
        by auto
      ultimately
      show ?thesis
        by auto
    next
      assume "x \<in> B - A"
      then have "x \<in> B" "x \<notin> A"
        by auto
      from `x \<in> B` have "x \<in> A \<union> B"
        by auto
      moreover
      from `x \<notin> A` have "x \<notin> A \<inter> B"
        by auto
      ultimately
      show ?thesis
        by auto
    qed
  qed



(* 3 *)
(* inverzna slika skupa funkcijom *)

(* 5 poena *)
lemma "A \<subseteq> f -` B \<longrightarrow> f ` A \<subseteq> B" 
proof
  assume *: "A \<subseteq> f -` B"
  show "f ` A \<subseteq> B"
  proof
    fix y
    assume "y \<in> f ` A"
    then obtain x where "x \<in> A" "f x = y"
      by auto
    from `x \<in> A` have "x \<in> f -` B"
      using *
      by auto
    then obtain y' where "f x = y'" "y' \<in> B"
      by auto
    from `f x = y` `f x = y'` `y' \<in> B`
    show "y \<in> B"
      by auto
  qed
qed



(* 4 *)
(* Funkcije - Isar *)

(* 5 poena *)
lemma
  assumes "inj (f \<circ> g)"
  shows "inj g"
  unfolding inj_def
proof safe
  fix x y
  assume "g x = g y"
  then have "f (g x) = f (g y)"
    by simp
  then have "(f \<circ> g) x = (f \<circ> g) y"
    by simp
  then show "x = y"
    using assms
    unfolding inj_def
    by auto
qed

(* 5 *)
(* MatematiДЌkom indukcijom dokazati da za prirodan broj n vaЕѕi naredna jednakost: \<open>1 + 3 +...+ (2*n+1) = (n+1) ^ 2. U dokazu koristiti samo simp i teoremu \<open>power2_sum\<close>. \<close>*)

thm power2_sum

(* 5 poena *)
lemma 
  fixes n :: nat
  shows "(\<Sum> k = 0..n. (2 * k + 1)) = (n + 1)^2"
proof (induction n)
  case 0
  show ?case
    by simp
next
  case (Suc n)
  have "(\<Sum>k = 0..Suc n. 2 * k + 1) = (\<Sum>k = 0..n. 2 * k + 1) + (2 * (n + 1) + 1)"
    by simp
  also have "\<dots> = (n + 1)^2 + (2 * (n + 1) + 1)"
    using Suc
    by simp
  also have "\<dots> = (n + 1)^2 + 1^2 + 2 * (n + 1) * 1"
    by simp
  also have "\<dots> = ((n + 1) + 1)^2"
    by (subst power2_sum[of "n+1"], rule refl)
  finally
  show ?case
    by simp
qed

end
