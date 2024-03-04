
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
  (*<*) oops (*>*)

text \<open>Uvodjenje disjunkcije: \<open>disjI1\<close>/\<open>disjI2\<close>\<close>

lemma "A \<or> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje implikacije: \<open>impI\<close>\<close>

lemma "A \<longrightarrow> B"
  (*<*) oops (*>*)

text \<open>Uvodjenje ekvivalencije: \<open>iffI\<close>\<close>

lemma "A \<longleftrightarrow> B"
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
  (*<*) oops (*>*)

lemma "A \<or> B \<longrightarrow> B \<or> A"
  (*<*) oops (*>*)

lemma "A \<and> B \<longrightarrow> A \<or> B"
  (*<*) oops (*>*)

lemma "(A \<and> B \<longrightarrow> C) \<longrightarrow> (A \<longrightarrow> (B \<longrightarrow> C))"
  (*<*) oops (*>*)

lemma "(A \<longrightarrow> (B \<longrightarrow> C)) \<longrightarrow> (A \<and> B \<longrightarrow> C)"
  (*<*) oops (*>*)

lemma "\<not> (A \<or> B) \<longrightarrow> \<not> A \<and> \<not> B"
  (*<*) oops (*>*)

lemma "\<not> A \<and> \<not> B \<longrightarrow> \<not> (A \<or> B)"
  (*<*) oops (*>*)

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  (*<*) oops (*>*)

text \<open>Dodatni primeri:\<close>

lemma "(Q \<longrightarrow> R) \<and> (R \<longrightarrow> P \<and> Q) \<and> (P \<longrightarrow> Q \<or> R) \<longrightarrow> (P \<longleftrightarrow> Q)"
  (*<*) oops (*>*)

lemma "(P \<longrightarrow> Q) \<and> (Q \<longrightarrow> R) \<longrightarrow> (P \<longrightarrow> Q \<and> R)"
  (*<*) oops (*>*)

lemma "(P \<longrightarrow> Q) \<and> \<not> Q \<longrightarrow> \<not> P"
  (*<*) oops (*>*)

lemma "(P \<longrightarrow> (Q \<longrightarrow> R)) \<longrightarrow> (Q \<longrightarrow> (P \<longrightarrow> R))"
  (*<*) oops (*>*)

lemma "\<not> (P \<and> \<not>P)"
  (*<*) oops (*>*)

lemma "A \<and> (B \<or> C ) \<longrightarrow> (A \<and> B) \<or> (A \<and> C)"
  (*<*) oops (*>*)

lemma "\<not> (A \<and> B) \<longrightarrow> (A \<longrightarrow> \<not> B)"
  (*<*) oops (*>*)

lemma "(A \<longrightarrow> C ) \<and> (B \<longrightarrow> \<not> C ) \<longrightarrow> \<not> (A \<and> B)"
  (*<*) oops (*>*)

lemma "(A \<and> B) \<longrightarrow> ((A \<longrightarrow> C ) \<longrightarrow> \<not> (B \<longrightarrow> \<not> C ))"
  (*<*) oops (*>*)

lemma "(A \<longleftrightarrow> B) \<longrightarrow> (\<not> A \<longleftrightarrow> \<not> B)"
  (*<*) oops (*>*)

lemma "A \<longrightarrow> \<not> \<not> A"
  (*<*) oops (*>*)

lemma "\<not> (A \<longleftrightarrow> \<not> A)"
  (*<*) oops (*>*)

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> B \<longrightarrow> \<not> A)"
  (*<*) oops (*>*)

lemma "\<not> A \<or> B \<longrightarrow> (A \<longrightarrow> B)"
  (*<*) oops (*>*)

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
  (*<*) oops (*>*)

text \<open>Eliminacija univerzalnog kvantifikatora: \<open>allE\<close>\<close>

lemma "\<forall> x. P x \<Longrightarrow> A"
  (*<*) oops (*>*)

text \<open>Uvođenje egzistencijalnog kvantifikatora: \<open>exI\<close>\<close>

lemma "\<exists> x. P x"
  (*<*) oops (*>*)

text \<open>Eliminacija egzistencijalnog kvantifikatora: \<open>exE\<close>\<close>

lemma "\<exists> x. P x \<Longrightarrow> A"
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Dokazi u prirodnoj dedukciji]\<close>

text \<open>Pokazati da su sledeće formule valjane u logici prvog reda. 
      Dozvoljeno je korišćenje samo intuicionističkih pravila prirodne dedukcije.\<close>

lemma "(\<forall> x. Man x \<longrightarrow> Mortal x) \<and> Man Socrates \<longrightarrow> Mortal Socrates"
  (*<*) oops (*>*)

lemma de_Morgan_1: "(\<exists> x. \<not> P x) \<longrightarrow> \<not> (\<forall> x. P x)"
  (*<*) oops (*>*)

lemma de_Morgan_2: "(\<forall> x. \<not> P x) \<longrightarrow> (\<nexists> x. P x)"
  (*<*) oops (*>*)

lemma de_Morgan_3: "(\<nexists> x. P x) \<longrightarrow> (\<forall> x. \<not> P x)"
  (*<*) oops (*>*)

lemma "(\<exists> x. P x) \<and> (\<forall> x. P x \<longrightarrow> Q x) \<longrightarrow> (\<exists> x. Q x)"
  (*<*) oops (*>*)

text \<open>Dodatni primeri:\<close>

lemma "(\<forall> m. Man m \<longrightarrow> Mortal m) \<and> 
       (\<forall> g. Greek g \<longrightarrow> Man g) \<longrightarrow>
       (\<forall> a. Greek a \<longrightarrow> Mortal a)"
  (*<*) oops (*>*)

lemma "(\<forall> a. P a \<longrightarrow> Q a) \<and> (\<forall> b. P b) \<longrightarrow> (\<forall> x. Q x)"
  (*<*) oops (*>*)

lemma "(\<exists> x. A x \<or> B x) \<longrightarrow> (\<exists> x. A x) \<or> (\<exists> x. B x)"
  (*<*) oops (*>*)

lemma "(\<forall> x. A x \<longrightarrow> \<not> B x) \<longrightarrow> (\<nexists> x. A x \<and> B x)"
  (*<*) oops (*>*)

text \<open>Formulisati i dokazati naredna tvrđenja.\<close>

text \<open>Ako za svaki broj koji nije paran važi da je neparan;\\
      i ako za svaki neparan broj važi da nije paran;\\
      pokazati da onda za svaki broj važi da nije istovremeno i paran i neparan.\<close>

text \<open>Ako je svaki kvadrat romb;\\
      i ako je svaki kvadrat pravougaonik;\\
      i ako znamo da postoji makar jedan kvadrat;\\
      onda postoji makar jedan romb koji je istovremeno i pravougaonik.\<close>

text \<open>Ako je relacija R simetrična, tranzitivna\\
      i ako za svako x postoji y koje je sa njim u relaciji,\\ 
      onda je relacija R i refleksivna.\<close>

text \<open>Savet: Pomoću ključne reči \<open>definition\<close> definisati osobinu refleksivnosti,
      tranzitivnosti i simetricnosti. Ta formulisati tvđenje i dokazati ga.
      Podsetiti se ključne reči \<open>unfolding\<close> za raspisivanje definicije.\<close>

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Klasična pravilo prirodne dedukcije: ccontr.]\<close>

text \<open>Diskutovati zašto sledeće tvrđenje može biti dokazano samo intuicionističkim pravilima 
      prirodne dedukcije, dok to ne važi za tvrđenje nakon njega. Primetiti razliku između 
      pravila \<open>notI\<close> i \<open>ccontr\<close>.\<close>

lemma \<open>A \<longrightarrow> \<not> \<not> A\<close>
  (*<*) oops (*>*)

lemma "\<not> \<not> A \<longrightarrow> A"
  (*<*) oops (*>*)

text \<open>Dokazati sledeća tvrđenja:\<close>

lemma "(\<not> P \<longrightarrow> P) \<longrightarrow> P"
  (*<*) oops (*>*)

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  (*<*) oops (*>*)

lemma "(\<not> (\<forall> x. P x)) \<longrightarrow> (\<exists> x. \<not> P x)"
  (*<*) oops (*>*)

text \<open>Dodatni primeri:\<close>

lemma "(\<not> B \<longrightarrow> \<not> A) \<longrightarrow> (A \<longrightarrow> B)"
  (*<*) oops (*>*)

lemma "(A \<longrightarrow> B) \<longrightarrow> (\<not> A \<or> B)"
  (*<*) oops (*>*)

lemma "(\<not> P \<longrightarrow> Q) \<longleftrightarrow> (\<not> Q \<longrightarrow> P)"
  (*<*) oops (*>*)

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

text_raw \<open>\begin{exercise}[subtitle=Klasična pravilo prirodne dedukcije: classical.]\<close>

text \<open>Pokazati naredna tvrđenja pomoću pravila \<open>classical\<close>. Zgodna alternativa ovog pravila je 
      razdvajanje na slučajeve neke podformule.\<close>

thm classical

lemma "P \<or> \<not> P"
  (*<*) oops (*>*)

lemma "(A \<longleftrightarrow> (A \<longleftrightarrow> B)) \<longrightarrow> B"
  (*<*) oops (*>*)

text \<open>\<open>Paradoks pijanca\<close>:\\
      Postoji osoba za koju važi, ako je on pijanac onda su i svi ostali pijanci.\<close>

lemma drinker's_paradox: "\<exists> x. drunk x \<longrightarrow> (\<forall> x. drunk x)"
  (*<*) oops (*>*)

text_raw \<open> \end{exercise} \<close>

(*<*)
end
(*>*)
