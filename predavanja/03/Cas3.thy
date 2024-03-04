theory Cas3
  imports Main 

begin

lemma 
  "(p \<or> q) \<and> r \<longrightarrow> (p \<and> r) \<or> (q \<and> r)"
  apply (rule impI)
  apply (erule conjE)
  (* moramo da dokazemo i u jednom i u drugom slucaju *)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption
   apply assumption
  apply (rule disjI2)
  apply (rule conjI)  
   apply assumption
  apply assumption
  done 


lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  apply (rule impI)
  apply (rule ccontr) (* kontradikcija, prebacuje mi na levu stranu *)
  apply (erule notE)
  apply (rule conjI)
   apply (rule ccontr)
  apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (rule ccontr)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done

(*
lemma "(\<forall> x. P x \<and> Q x) \<longrightarrow> (\<forall> x. P x) \<and> (\<forall> x. Q x)"
  apply (rule impI)
  apply (rule conjI)
   apply (rule allI)
   apply (erule_tac x="y" in allE)
   apply (erule conjE)
   apply assumption 
   apply (rule allI)
  apply (erule_tac x="z" in allE)
   apply (erule conjE)
   apply assumption 
  done 
*)

lemma "(\<exists> x. P x \<or> Q x) \<longrightarrow> (\<exists> y. P y) \<or> (\<exists> z. Q z)"
  apply (rule impI)
  apply (erule exE)
  apply (erule disjE) (* ne smemo o x-u da znamo nista dodatno *)
   apply (rule disjI1)
   apply (rule_tac x="x" in exI)
   apply assumption
  apply (rule disjI2)
  apply (rule_tac x="x" in exI)
  apply assumption  
  done 

(*
 TEOREMA O SREDNJIJ VREDNOSTI

LAGRANZ:
  [a, b] 
\<exists> c \<in> [a, b] . f'(c) = (f(b) - f(a)) / (b - a)

KOSIJEVA TEOREMA:
[a, b], f, g

\<exists> c \<in> [a, b]. f'(c) / g'(c) = (f(b) - f(a)) / (g(b) - g(a))

f'(c) = (f(b) - f(a)) / (b - a)
g'(c1) = (g(b) - g(a)) / (b - a)

ovo vazi za bilo koje c, ne znamo da li su bas ta dva c ekvivalentna

*)

lemma "\<not> (\<exists> x. P x) \<longrightarrow> (\<forall> x. \<not> P x)"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply assumption
  done

lemma "\<not> (\<forall> x. P x) \<longrightarrow> (\<exists> x. \<not> P x)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply assumption 
  done 



end 