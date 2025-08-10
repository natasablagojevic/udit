
(*<*)
theory Vezbe03
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Intuicionistička pravila prirodne dedukcije u iskaznoj logici]\<close>

text \<open>Diskutovati o pravilima uvođenja i pravilima eliminacije prirodne dedukcije iskazne logike.
      Pomoću ključne reči @{text "thm"} ispitati svako pravilo prirodne dedukcije. Primeniti 
      odgovarajuće pravilo prirodne dedukcije na jednostavnim formulama i diskutovati o cilju
      koga treba dokazati pre i posle primene tog pravila.\<close>

text \<open>Uvodjenje konjukcije: \<open>conjI\<close>\<close>

lemma "A \<and> B"
  apply (rule conjI)
  (*<*) oops (*>*)

text \<open>Uvodjenje disjunkcije: \<open>disjI1\<close>/\<open>disjI2\<close>\<close>

lemma "A \<or> B"
  apply (rule disjI1)
  (*<*) oops (*>*)

text \<open>Uvodjenje implikacije: \<open>impI\<close>\<close>

lemma "A \<longrightarrow> B"
  apply (rule impI)
  (*<*) oops (*>*)

text \<open>Uvodjenje ekvivalencije: \<open>iffI\<close>\<close>

lemma "A \<longleftrightarrow> B"
  apply (rule iffI)
  (*<*) oops (*>*)

text \<open>Uvodjenje negacije: \<open>notI\<close>\<close>

lemma "\<not> A"
  (*<*) oops (*>*)

text \<open>Eliminacija konjukcije. \<open>conjE\<close>\<close>

lemma "A \<and> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija disjunkcije. \<open>disjE\<close>\<close>

lemma "A \<or> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija implikacije. \<open>impE\<close>\<close>

lemma "A \<longrightarrow> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija ekvivalencije. \<open>iffE\<close>\<close>

lemma "A \<longleftrightarrow> B \<Longrightarrow> C"
  (*<*) oops (*>*)

text \<open>Eliminacija negacije. \<open>notE\<close>\<close>

lemma "\<not> A \<Longrightarrow> B" 
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Dokazi u prirodnoj dedukciji]\<close>

text \<open>Pokazati da su sledeće formule tautologija u iskaznoj logici. 
      Dozvoljeno je korišćenje samo intuicionističkih pravila prirodne dedukcije.\<close>

lemma "A \<and> B \<longrightarrow> B \<and> A"
  apply (rule impI)
  apply (erule conjE)
  apply (rule conjI)
   apply assumption+
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
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption+
  done 

lemma "\<not> (A \<or> B) \<longrightarrow> \<not> A \<and> \<not> B"
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

lemma "\<not> A \<and> \<not> B \<longrightarrow> \<not> (A \<or> B)"
  apply (rule impI)
  apply (rule notI)
  apply (erule conjE)
  apply (erule disjE)
   apply (erule notE)
   apply assumption
  apply (erule notE) back 
  apply assumption
  done 

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  apply (rule notI)
  apply (erule iffE)
  apply (erule impE)
   apply (rule ccontr)
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption 
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

text \<open>Dodatni primeri:\<close>

lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  apply (rule impI)
  apply (erule conjE)+
  apply (rule iffI)
   apply (rule ccontr)
   apply (erule impE) back back 
    apply assumption
   apply (erule disjE)
    apply (erule impE)
     apply assumption
    apply (erule notE)
    apply assumption 
   apply (erule impE) back 
    apply assumption 
   apply (erule conjE)
   apply (erule notE)
   apply assumption 
  apply (erule impE) 
   apply assumption 
  apply (erule impE)
   apply assumption
  apply (erule conjE)
  apply assumption 
  done 

lemma "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<and> R)"
  apply (rule impI)+
  apply (erule conjE)
  apply (rule conjI)
   apply (erule impE)
    apply assumption+
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption+
  done 

lemma "(P \<longrightarrow> Q) \<and> \<not> Q \<longrightarrow> \<not> P"
  apply (rule impI)
  apply (erule conjE)
  apply (rule notI)
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
   apply assumption+
  done 

lemma "\<not> (P \<and> \<not>P)"
  apply (rule notI)
  apply (erule conjE)
  apply (erule notE)
  apply assumption
  done 

lemma "A \<and> (B \<or> C ) \<longrightarrow> (A \<and> B) \<or> (A \<and> C)"
  apply (rule impI)
  apply (erule conjE)
  apply (erule disjE)
   apply (rule disjI1)
   apply (rule conjI)
    apply assumption+
  apply (rule disjI2)
  apply (rule conjI)
   apply assumption+
  done 

lemma "\<not> (A \<and> B) \<longrightarrow> (A \<longrightarrow> \<not> B)"
  apply (rule impI)+
  apply (rule notI)
  apply (erule notE)
  apply (rule conjI)
   apply assumption+
  done 

lemma "(A \<longrightarrow> C ) \<and> (B \<longrightarrow> \<not> C ) \<longrightarrow> \<not> (A \<and> B)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "(A \<and> B) \<longrightarrow> ((A \<longrightarrow> C ) \<longrightarrow> \<not> (B \<longrightarrow> \<not> C ))"
  apply (rule impI)+
  apply (erule conjE)
  apply (rule notI)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "(A \<longleftrightarrow> B) \<longrightarrow> (\<not> A \<longleftrightarrow> \<not> B)"
  apply (rule impI)
  apply (erule iffE)
  apply (rule iffI)
   apply (rule notI)
   apply (erule impE)+
     apply assumption+
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (rule notI)
  apply (erule impE) 
   apply assumption
  apply (erule notE)
  apply assumption
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
  apply (erule impE)
   apply (rule ccontr)
   apply (erule impE)
    apply assumption
   apply (erule notE)
   apply assumption
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> \<not> A)"
  apply (rule impI)+
  apply (rule notI)
  apply (erule impE)
  apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "\<not> A \<or> B \<longrightarrow> (A \<longrightarrow> B)"
  apply (rule impI)+
  apply (rule ccontr)
  apply (erule disjE)
   apply (erule notE) back 
   apply assumption
  apply (erule notE)
  apply assumption
  done 

  text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Intuicionistička pravila prirodne dedukcije u logici prvog reda]\<close>

text \<open>Diskutovati o pravilima uvođenja i pravilima eliminacije prirodne dedukcije u logici 
      prvog reda. Pomoću ključne reči @{text "thm"} ispitati svako pravilo prirodne dedukcije. 
      Primeniti odgovarajuće pravilo prirodne dedukcije na jednostavnim formulama i diskutovati 
      o cilju koga treba dokazati pre i posle primene tog pravila.\<close>

text \<open>Za logiku prvog reda pored pravila prirodne dedukcije iskazne 
      logike, važe i pravila uvođenja i elimenacije kvantifikatora.\<close>

text \<open>Uvođenje univerzalnog kvantifikatora: \<open>allI\<close>\<close>

lemma "\<forall> x. P x"
  apply (rule allI)
  (*<*) oops (*>*)

text \<open>Eliminacija univerzalnog kvantifikatora: \<open>allE\<close>\<close>

lemma "\<forall> x. P x \<Longrightarrow> A"
  apply (erule_tac x="x" in allE)
  (*<*) oops (*>*)

text \<open>Uvođenje egzistencijalnog kvantifikatora: \<open>exI\<close>\<close>

lemma "\<exists> x. P x"
  apply (rule_tac x="x" in exI)
  (*<*) oops (*>*)

text \<open>Eliminacija egzistencijalnog kvantifikatora: \<open>exE\<close>\<close>

lemma "\<exists> x. P x \<Longrightarrow> A"
  apply (erule exE)
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Dokazi u prirodnoj dedukciji]\<close>

text \<open>Pokazati da su sledeće formule valjane u logici prvog reda. 
      Dozvoljeno je korišćenje samo intuicionističkih pravila prirodne dedukcije.\<close>

lemma "(\<forall> x. Man x \<longrightarrow> Mortal x) \<and> Man Socrates \<longrightarrow> Mortal Socrates"
  apply (rule impI)
  apply (erule conjE)
  apply (erule_tac x="Socrates"  in allE)
  apply (erule impE)
   apply assumption+
  done 

lemma de_Morgan_1: "(\<exists> x. \<not> P x) \<longrightarrow> \<not> (\<forall> x. P x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption
  done 

lemma de_Morgan_2: "(\<forall> x. \<not> P x) \<longrightarrow> (\<nexists> x. P x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule notE)
  apply assumption
  done 

lemma de_Morgan_3: "(\<nexists> x. P x) \<longrightarrow> (\<forall> x. \<not> P x)"
  apply (rule impI)
  apply (rule allI)
  apply (rule notI)
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply assumption 
  done 

lemma "(\<exists> x. P x) \<and> (\<forall> x. P x \<longrightarrow> Q x) \<longrightarrow> (\<exists> x. Q x)"
  apply (rule impI)
  apply (erule conjE)
  apply (erule exE)
  apply (rule_tac x="x" in exI)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption+
  done 

text \<open>Dodatni primeri:\<close>

lemma "(\<forall> m. Man m \<longrightarrow> Mortal m) \<and> 
       (\<forall> g. Greek g \<longrightarrow> Man g) \<longrightarrow>
       (\<forall> a. Greek a \<longrightarrow> Mortal a)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="a" in allE)+
  apply (rule impI)
  apply (erule impE)+
    apply assumption+
  done 

lemma "(\<forall> a. P a \<longrightarrow> Q a) \<and> (\<forall> b. P b) \<longrightarrow> (\<forall> x. Q x)"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="x" in allE)+
  apply (erule impE)
   apply assumption+
  done 

lemma "(\<exists> x. A x \<or> B x) \<longrightarrow> (\<exists> x. A x) \<or> (\<exists> x. B x)"
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

lemma "(\<forall> x. A x \<longrightarrow> \<not> B x) \<longrightarrow> (\<nexists> x. A x \<and> B x)"
  apply (rule impI)
  apply (rule notI)
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule conjE)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

text \<open>Formulisati i dokazati naredna tvrđenja.\<close>

text \<open>Ako za svaki broj koji nije paran važi da je neparan;\\
      i ako za svaki neparan broj važi da nije paran;\\
      pokazati da onda za svaki broj važi da nije istovremeno i paran i neparan.\<close>

(*

paran(x) = x je paran 
neparan(x) = x je neparan 

\<forall>x. \<not> paran x \<longrightarrow> neparan x 
\<forall>x. neparan x \<longrightarrow> \<not> paran x 
\<longrightarrow> \<forall>x. \<not> (paran x \<and> neparan x)

*)

lemma "(\<forall>x. \<not> paran x \<longrightarrow> neparan x) \<and> (\<forall>x. neparan x \<longrightarrow> \<not> paran x) \<longrightarrow> (\<forall>x. \<not> (paran x \<and> neparan x))"
  by auto

lemma "(\<forall>x. \<not> paran x \<longrightarrow> neparan x) \<and> (\<forall>x. neparan x \<longrightarrow> \<not> paran x) \<longrightarrow> (\<forall>x. \<not> (paran x \<and> neparan x))"
  apply (rule impI)
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="x" in allE)+
  apply (rule notI)
  apply (erule conjE)
  apply (erule impE)+
    apply assumption+
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

text \<open>Ako je svaki kvadrat romb;\\
      i ako je svaki kvadrat pravougaonik;\\
      i ako znamo da postoji makar jedan kvadrat;\\
      onda postoji makar jedan romb koji je istovremeno i pravougaonik.\<close>

(*

kvadrat(x) = x je kvadrat 
romb(x) = x je romb 
pravougaonik(x) = x je pravougaonik 

\<forall>x. kvadrat x \<longrightarrow> romb x 
\<forall>x. kvadrat x \<longrightarrow> pravougaonik x 
\<exists>x. kvadrat x 

\<longrightarrow> \<exists>x. romb x \<and> pravougaonik x

*)

lemma "(\<forall>x. kvadrat x \<longrightarrow> romb x) \<and> (\<forall>x. kvadrat x \<longrightarrow> pravougaonik x) \<and> (\<exists>x. kvadrat x) \<longrightarrow> (\<exists>x. romb x \<and> pravougaonik x)"
  by auto 

lemma "(\<forall>x. kvadrat x \<longrightarrow> romb x) \<and> (\<forall>x. kvadrat x \<longrightarrow> pravougaonik x) \<and> (\<exists>x. kvadrat x) \<longrightarrow> (\<exists>x. romb x \<and> pravougaonik x)"
  apply (rule impI)
  apply (erule conjE)+
  apply (erule exE)
  apply (rule_tac x="x" in exI)
  apply (erule_tac x="x" in allE)+
  apply (rule conjI)
   apply (erule impE)
    apply assumption+
  apply (erule impE) back 
   apply assumption+
  done 

text \<open>Ako je relacija R simetrična, tranzitivna\\
      i ako za svako x postoji y koje je sa njim u relaciji,\\ 
      onda je relacija R i refleksivna.\<close>

(*

simetricna:   \<forall>x y. R x y \<longrightarrow> R y x 
tranzitivna:  \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z 
refleksivna:  \<forall>x. R x x 

simetricna \<and> tranzitivna \<and> (\<forall>x. \<exists>y. R x y) \<longrightarrow> refleksivna 

*)

definition "simetricna R \<equiv> \<forall>x y. R x y \<longrightarrow> R y x"
definition "tranzitivna R \<equiv> \<forall>x y z. R x y \<and> R y z \<longrightarrow> R x z"
definition "refleksivna R \<equiv> \<forall>x. R x x"

lemma "(simetricna R) \<and> (tranzitivna R) \<and> (\<forall>x. \<exists>y. R x y) \<longrightarrow> refleksivna R"
  unfolding simetricna_def tranzitivna_def refleksivna_def
  by auto 

lemma "(simetricna R) \<and> (tranzitivna R) \<and> (\<forall>x. \<exists>y. R x y) \<longrightarrow> refleksivna R"
  unfolding simetricna_def tranzitivna_def refleksivna_def
  apply (rule impI)
  apply (erule conjE)+
  apply (rule allI)
  apply (erule_tac x="x" in allE) back back 
  apply (erule exE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="y" in allE)
  apply (erule_tac x="x" in allE)
  apply (erule impE)
   apply assumption
  apply (erule impE)
   apply (rule conjI)
  apply assumption+
  done 


text \<open>Savet: Pomoću ključne reči \<open>definition\<close> definisati osobinu refleksivnosti,
      tranzitivnosti i simetricnosti. Ta formulisati tvđenje i dokazati ga.
      Podsetiti se ključne reči \<open>unfolding\<close> za raspisivanje definicije.\<close>

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Klasična pravilo prirodne dedukcije: ccontr.]\<close>

text \<open>Diskutovati zašto sledeće tvrđenje može biti dokazano samo intuicionističkim pravilima 
      prirodne dedukcije, dok to ne važi za tvrđenje nakon njega. Primetiti razliku između 
      pravila \<open>notI\<close> i \<open>ccontr\<close>.\<close>

lemma \<open>A \<longrightarrow> \<not> \<not> A\<close>
  apply (rule impI)
  apply (rule notI)
  apply (erule notE)
  apply assumption
  done 

lemma "\<not> \<not> A \<longrightarrow> A"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (assumption)
  done 

text \<open>Dokazati sledeća tvrđenja:\<close>

lemma "(\<not> P \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  apply (rule impI)
  apply (rule ccontr)
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

lemma "(\<not> (\<forall> x. P x)) \<longrightarrow> (\<exists> x. \<not> P x)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule allI)
  apply (rule ccontr)
  apply (erule notE)
  apply (rule_tac x="x" in exI)
  apply assumption
  done 

text \<open>Dodatni primeri:\<close>

lemma "(\<not> B \<longrightarrow> \<not> A) \<longrightarrow> (A \<longrightarrow> B)"
  apply (rule impI)+
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE) back 
  apply assumption
  done 

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> A \<or> B)"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply (rule ccontr)
   apply (erule notE)
   apply (rule disjI1)
   apply assumption
  apply (erule notE)
  apply (rule disjI2)
  apply assumption
  done 

lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  apply (rule iffI)
   apply (rule impI)
   apply (rule ccontr)
   apply (erule impE)
  apply assumption
   apply (erule notE)
   apply assumption
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply assumption
  apply (erule notE)
  apply assumption 
  done 

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  apply (rule impI)
  apply (rule ccontr)
  apply (erule impE)
   apply (rule impI)
   apply (erule notE)
   apply assumption
  apply (erule notE)
  apply assumption
  done 

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Klasična pravilo prirodne dedukcije: classical.]\<close>

text \<open>Pokazati naredna tvrđenja pomoću pravila \<open>classical\<close>. Zgodna alternativa ovog pravila je 
      razdvajanje na slučajeve neke podformule.\<close>

thm classical

lemma "P \<or> \<not> P"
  apply (rule classical)
  (*<*) oops (*>*)

lemma "(A \<longleftrightarrow> (A \<longleftrightarrow> B)) \<longrightarrow> B"
  apply (rule impI)
  apply (rule classical)
  apply (erule iffE)
  apply (erule impE) 
   apply (rule classical)
   apply (erule impE)
    apply (rule iffI)
     apply (erule notE) back 
     apply assumption
    apply (erule notE)
    apply assumption
   apply assumption
  apply (rule classical)
  apply (erule impE)
   apply (rule iffI)
    apply (erule iffE)
    apply (erule impE)
     apply assumption+
   apply (erule iffE)
   apply (erule impE) back 
    apply assumption+
  apply (erule iffE)
  apply (erule impE)
   apply assumption+
  done 

text \<open>\<open>Paradoks pijanca\<close>:\\
      Postoji osoba za koju važi, ako je on pijanac onda su i svi ostali pijanci.\<close>

lemma drinker's_paradox: "\<exists> x. drunk x \<longrightarrow> (\<forall> x. drunk x)"
  (*<*) oops (*>*)

lemma "\<lbrakk>P = P'; (P' \<longrightarrow> Q = Q')\<rbrakk> \<Longrightarrow> (P \<and> Q) = (P' \<and> Q')"
  apply (rule iffI)
   apply (erule conjE)
   apply (rule conjI)
    apply (erule impE) 
     apply (erule iffE)
     apply (erule impE)
      apply assumption+
    apply (erule iffE)
    apply (erule impE)
     apply assumption+
   apply (erule impE)
    apply (erule iffE)
    apply (erule impE)
     apply assumption+
   apply (erule iffE) back 
   apply (erule impE)
    apply assumption+
  apply (erule conjE)
  apply (rule conjI)
   apply (erule iffE)
   apply (erule impE) back back 
    apply assumption+
  apply (erule impE) 
   apply assumption
  apply (erule iffE) back 
  apply (erule impE) back 
   apply assumption+
  done 

lemma "(\<forall> x. P x \<and> Q x) \<longleftrightarrow> (\<forall> x. P x) \<and> (\<forall> x. Q x)"
  apply (rule iffI)
   apply (rule conjI)
    apply (rule allI)
    apply (erule_tac x="x" in allE)
    apply (erule conjE)
    apply assumption
   apply (rule allI)
   apply (erule_tac x="x" in allE)
   apply (erule conjE)
   apply assumption
  apply (erule conjE)
  apply (rule allI)
  apply (erule_tac x="x" in allE)+
  apply (rule conjI)
   apply assumption+
  done 


text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
