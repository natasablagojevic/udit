theory Cas3
  imports Main

begin

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (rule conjI)
   apply (erule conjE)
   apply assumption 
  apply (erule conjE)
  apply assumption
  done 

lemma "A \<or> B \<longrightarrow> B \<or> A"
  apply (rule impI)
  apply (erule disjE)
   apply (rule disjI2)
   apply assumption
  apply (rule disjI1)
  apply assumption 
  done 

lemma "A \<and> B \<longrightarrow> A \<or> B"
  apply (rule impI)
  apply (erule conjE)
  apply (rule disjI1)
  apply assumption
  done 

lemma "(A \<and> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  apply (rule impI)+
  apply (erule impE)
   apply (rule conjI)
    apply assumption+
  done 

lemma "(A \<longrightarrow> (B \<longrightarrow> C)) \<longrightarrow> (A \<and> B \<longrightarrow> C)"
  apply (rule impI)+
  apply (erule impE)
   apply (erule conjE)
   apply assumption
  apply (erule impE)
   apply (erule conjE)
   apply assumption+
  done 

lemma "\<not>(A \<or> B) \<longrightarrow> \<not> A \<and> \<not> B"
  apply (rule impI)
  apply (rule conjI)
   apply (rule notI)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption 
  apply (rule notI)
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done 

lemma "\<not>A \<and> \<not>B \<longrightarrow> \<not>(A \<or> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply (erule notE) back
  apply assumption
  done 

lemma "\<not>(A \<longleftrightarrow> \<not>A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) back 
   apply (rule notI)
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption 
  done 

lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  apply (rule impI)
  apply (rule iffI)
   apply (erule conjE)+
   apply (erule impE) back back 
    apply assumption 
   apply (erule impE) 
    apply (erule disjE)
     apply assumption 
    apply (erule impE) 
     apply assumption 
    apply (erule conjE)
    apply assumption 
   apply (erule disjE)
    apply assumption 
   apply (erule impE)
    apply assumption 
   apply (erule conjE)
   apply assumption 
  apply (erule conjE)+
  apply (erule impE) back
   apply (erule impE)
    apply assumption +
  apply (erule conjE)
  apply assumption
  done 

lemma "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<and> R)"
  apply (rule impI)+
  apply (rule conjI)
   apply (erule conjE)
   apply (erule impE)
    apply assumption +
  apply (erule conjE)
  apply (erule impE)
  apply assumption
  apply (erule impE)
   apply assumption +
  done 

lemma "(P \<longrightarrow> Q) \<and> \<not> Q \<longrightarrow> \<not> P"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> (Q \<longrightarrow> (P \<longrightarrow> R))"
  apply (rule impI)+
  apply (erule impE)
   apply assumption 
  apply (erule impE)
   apply assumption +
  done 

lemma "\<not> (P \<and> \<not>P )"
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done 

lemma "A \<and> (B \<or> C ) \<longrightarrow> (A \<and> B ) \<or> (A \<and> C )"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption +
  apply (rule disjI2)
  apply (rule conjI)
   apply assumption+
  done 

lemma "\<not> (A \<and> B ) \<longrightarrow> (A \<longrightarrow> \<not> B )"
  apply (rule impI)+
  apply (rule notI)
  apply (erule notE)
  apply (rule conjI)
   apply assumption+
  done 

lemma "(A \<longrightarrow> C ) \<and> (B \<longrightarrow> \<not> C ) \<longrightarrow> \<not> (A \<and> B )"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)+
  apply (erule impE)
   apply assumption 
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "(A \<and> B ) \<longrightarrow> ((A \<longrightarrow> C ) \<longrightarrow> \<not> (B \<longrightarrow> \<not> C ))"
  apply (rule impI)+
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)+
    apply assumption +
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done 

lemma "(A \<longleftrightarrow> B ) \<longrightarrow> (\<not> A \<longleftrightarrow> \<not> B )"
  apply (rule impI)
  apply (rule iffI)
   apply (rule notI)
   apply (erule iffE)
   apply (erule notE)
   apply (erule impE) back
    apply assumption+
  apply (rule notI)
  apply (erule iffE)
  apply (erule notE)
  apply (erule impE) 
   apply assumption +
  done 

lemma "A \<longrightarrow> \<not> \<not> A"
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption 
  done 

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE) back
   apply (rule notI)
   apply (erule impE)
    apply assumption 
   apply (erule notE)
   apply assumption 
  apply (erule impE)
  apply assumption 
  apply (erule notE)
  apply assumption 
  done 

lemma "(A \<longrightarrow> B ) \<longrightarrow> (\<not> B \<longrightarrow> \<not> A)"
  apply (rule impI)+
  apply (rule notI)
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done 

lemma "\<not> A \<or> B \<longrightarrow> (A \<longrightarrow> B )"
  apply (rule impI)+
  apply (erule disjE)
   apply (erule notE)
   apply assumption+
  done 

lemma "(\<forall> x . Man x \<longrightarrow> Mortal x ) \<and> Man Socrates \<longrightarrow> Mortal Socrates"
  apply (rule impI)
  apply (erule conjE)
  apply (erule_tac x = "Socrates" in allE)
  apply (erule impE)
   apply assumption+
  done 

lemma "(\<exists> x . \<not> P x ) \<longrightarrow> \<not> (\<forall> x . P x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption 
  done 

lemma "(\<forall> x . \<not> P x ) \<longrightarrow> (\<nexists> x . P x )"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption 
  done 

lemma "(\<nexists> x . P x ) \<longrightarrow> (\<forall> x . \<not> P x )"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply assumption 
  done 

lemma "(\<exists> x . P x ) \<and> (\<forall> x . P x \<longrightarrow> Q x ) \<longrightarrow> (\<exists> x . Q x )"
  apply (rule impI)
  apply (erule conjE)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (rule_tac x ="x" in exI)
  apply (erule impE)
   apply assumption +
  done 

lemma "(\<forall> m. Man m \<longrightarrow> Mortal m) \<and> (\<forall> g. Greek g \<longrightarrow> Man g) \<longrightarrow> (\<forall> a. Greek a \<longrightarrow> Mortal a)"
  apply (rule impI)
  apply (rule allI)
  apply (rule impI)
  apply (erule conjE)
  apply (erule_tac x="a" in allE) 
  apply (erule impE)
  apply (erule_tac x="a" in allE)
   apply (erule impE)
    apply assumption+
  done 

lemma "(\<forall> a. P a \<longrightarrow> Q a) \<and> (\<forall> b. P b) \<longrightarrow> (\<forall> x . Q x )"
  apply (rule impI)
  apply (rule allI)
  apply (erule conjE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
  apply (erule_tac x="x" in allE)
   apply assumption +
  done 

lemma "(\<exists> x . A x \<or> B x ) \<longrightarrow> (\<exists> x . A x ) \<or> (\<exists> x . B x )"
  apply (rule impI)
  apply (erule exE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule_tac x="x" in exI)
   apply assumption 
  apply (rule disjI2)
  apply (rule_tac x="x" in exI)
  apply assumption 
  done 

lemma "(\<forall> x . A x \<longrightarrow> \<not> B x ) \<longrightarrow> (\<nexists> x . A x \<and> B x )"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply (erule conjE)
   apply assumption 
  apply (erule conjE)
  apply (erule notE)
  apply assumption 
  done 

(*--------------------------------------------------------------*)

(*
Ako za svaki broj koji nije paran važi da je neparan;
i ako za svaki neparan broj važi da nije paran;
pokazati da onda za svaki broj važi da nije istovremeno i paran i neparan

paran(x) = x je paran 
neparan(x) = x je neparan 

\<forall>x. \<not>paran x \<longrightarrow> neparan x 
\<forall>x. neparan x \<longrightarrow> \<not> paran x 
-----------------------------
\<forall>x. \<not>(paran x \<and> neparan x)

(\<forall>x. \<not>paran x \<longrightarrow> neparan x) \<and> (\<forall>x. neparan x \<longrightarrow> \<not> paran x) \<longrightarrow> (\<forall>x. \<not>(paran x \<and> neparan x))
*)

lemma "(\<forall>x. \<not>paran x \<longrightarrow> neparan x) \<and> (\<forall>x. neparan x \<longrightarrow> \<not> paran x) \<longrightarrow> (\<forall>x. \<not>(paran x \<and> neparan x))"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule conjE)+
  apply (erule_tac x="x" in allE)+
  apply (erule impE)+
    apply assumption+ 
  apply (erule impE)
   apply assumption 
  apply (erule notE)
  apply assumption 
  done 

(*--------------------------------------------------------------------------------------------------------*)

(*
Ako svaki konj ima potkovice;
i ako ne postoji čovek koji ima potkovice;
i ako znamo da postoji makar jedan čovek;
dokazati da postoji čovek koji nije konj.

konj(x) = x je konj 
covek(x) = x je covek 
potkovice(x) = x ima potkovice 

-------------------------
\<forall>x. konj x \<longrightarrow> potkovice x 
\<nexists>x. covek x \<and> potkovice x 
\<exists>x. covek x 
----------------------------
\<exists>x. covek x \<and> \<not> konj x

(\<forall>x. konj x \<longrightarrow> potkovice x) \<and> (\<nexists>x. covek x \<and> potkovice x) \<and> (\<exists>x. covek x) \<longrightarrow> (\<exists>x. covek x \<and> \<not> konj x)
*)

lemma "(\<forall>x. konj x \<longrightarrow> potkovice x) \<and> (\<nexists>x. covek x \<and> potkovice x) \<and> (\<exists>x. covek x) \<longrightarrow> (\<exists>x. covek x \<and> \<not> konj x)"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption 
  apply (rule notI)
  apply (erule impE)
  apply assumption 
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
   apply assumption +
  done 

(*-----------------------------------------------------------------------------------------------------------------------*)

(*
Ako je svaki kvadrat romb;
i ako je svaki kvadrat pravougaonik;
i ako znamo da postoji makar jedan kvadrat;
onda postoji makar jedan romb koji je istovremeno i pravougaonik.

kvadrat(x) = x je kvadrat 
romb(x) = x je romb
pravougaonik(x) = x je pravougaonik 

-------------------------------------
\<forall>x. kvadrat x \<longrightarrow> romb x 
\<forall>x. kvadrat x \<longrightarrow> pravougaonik x
\<exists>x. kvadrat x 
----------------------------
\<exists>x. romb x \<and> pravougaonik x

(\<forall>x. kvadrat x \<longrightarrow> romb x) \<and> (\<forall>x. kvadrat x \<longrightarrow> pravougaonik x) \<and> (\<exists>x. kvadrat x) \<longrightarrow> (\<exists>x. romb x \<and> pravougaonik x)
*)

lemma "(\<forall>x. kvadrat x \<longrightarrow> romb x) \<and> (\<forall>x. kvadrat x \<longrightarrow> pravougaonik x) \<and> (\<exists>x. kvadrat x) \<longrightarrow> (\<exists>x. romb x \<and> pravougaonik x)"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule exE)
  apply (erule_tac x="x" in allE)+
  apply (rule_tac x="x" in exI)
  apply (rule conjI)
  apply (erule impE)+
     apply assumption+
  apply (erule impE)+
    apply assumption +
  apply (erule impE)
   apply assumption +
  done 

(*---------------------------------------------------------------------------------------------------------------------*)

(*
Ako je relacija R simetrična, tranzitivna
i ako za svako x postoji y koje je sa njim u relaciji,
onda je relacija R i refleksivna.

simetricna(x) = x je simpetricna 
tranzitivna(x) = x je tranzitivna 
refleksivna(x) = x je refleksivna 

----------------------------

(simetricna R \<and> tranzitivna R) \<and> (\<forall>x. \<exists>y. R x y) \<longrightarrow> refleksivna R
*)

definition "refleksivna R \<equiv> \<forall>x. R x x"
definition "simetricna R \<equiv> \<forall>x y. R x y \<longleftrightarrow> R y x"
definition "tranzitivna R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"

lemma "(simetricna R \<and> tranzitivna R) \<and> (\<forall>x. \<exists>y. R x y) \<longrightarrow> refleksivna R"
  unfolding simetricna_def tranzitivna_def refleksivna_def
  apply (rule impI)
  apply (rule allI)
  apply (erule conjE)+
  apply (erule_tac x="x" in allE)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule iffE)
  apply (erule impE)
  apply (rule conjI)
  apply assumption 
   apply (erule impE) back 
  apply (erule impE)
     apply assumption + 
   apply (erule impE) 
    apply assumption + 
  done 








end