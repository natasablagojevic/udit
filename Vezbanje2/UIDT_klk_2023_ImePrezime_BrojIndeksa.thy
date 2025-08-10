
(*<*)
theory UIDT_klk_2023_ImePrezime_BrojIndeksa
    imports Main
begin
(*>*)

text \<open>\<open>Pravila igre\<close>: 
      Promeniti ime teorije i naziv fajla u \<open>UIDT_klk_2023_ImePrezime_BrojIndeksa\<close>, 
      gde ime, prezime i broj indeksa treba zameniti svojim podacima. 
      Na primer, za studenta Marka Markovića čiji je broj indeksa 205/2022, 
      ime teorije je \<open>UIDT_klk_2023_MarkoMarkovic_mi22205\<close>,
      a ime fajla \<open>UIDT_klk_2023_MarkoMarkovic_mi22205.thy\<close>.\<close>

text  \<open>Nije dozvoljeno korisćenje \<open>sledgehammer\<close>-a. Ispit traje 1 sat i 30 minuta. \<open>Srećno!\<close>\<close>


text_raw \<open>\begin{exercise}[subtitle={Prirodna dedukcija u logici}, points=6]\<close>

text \<open>Pokazati tautalogičnost sledeće formule u iskaznoj logici koristeći 
      pravila prirodne dedukcije u okviru apply dokaza.\<close>

lemma "\<lbrakk>P = P'; (P' \<longrightarrow> Q = Q')\<rbrakk> \<Longrightarrow> (P \<and> Q) = (P' \<and> Q')"
  apply (rule iffI)
   apply (erule conjE)
   apply (rule conjI)
    apply (erule iffE)
    apply (erule impE) back 
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
   apply (erule impE)
    apply assumption
   apply (erule iffE)
   apply (erule impE) back 
    apply assumption+
  apply (erule impE)
   apply assumption 
  apply (erule iffE) back 
  apply (erule impE) back 
   apply assumption+
  done 

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle={Prirodna dedukcija u logici}, points=6]\<close>

text \<open>Pokazati valjanost sledeće rečenice u logici prvog reda koristeći
      prirodnu dedukciju u okviru apply dokaza.\<close>

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

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle={Svojstva funkcija}, points=6]\<close>

text \<open>Napisati detaljan Isar dokaz sledeće leme o slici i inverznoj slici funkcije.\<close>

lemma "f ` f -` f ` A \<subseteq> f ` A"
proof
  fix y
  assume "y \<in> f ` f -` f ` A" 
  then obtain x where "x \<in> f -` f ` A" "f x = y" by auto
  from this have "f x \<in> f ` A" by auto 
  from this show "y \<in> f ` A" using \<open>f x = y\<close> by auto 
qed

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle={Logika}, points=6]\<close>

text \<open>Edgar Abercrombie bio je antropolog koga je posebno zanimala logika, 
      sociologija i laž i istina. Jednog dana odlučio je posetiti ostrva 
      gde se odvijalo puno aktivnosti laganja i govorenja istine! 
      Prvo ostrvo koje je posetio bio je Otok vitezova i podanika
      na kojem su oni zvani vitezovi uvek govorili istinu i oni zvani 
      podanici uvek lažu. 
      Dodatno znao je da je svaki stanovnik ili vitez ili podanik.\<close>

text \<open>Abercrombie je sreo samo dva stanovnika A i B.
      A je rekao: Bar jedan od nas je podanik.
      Šta možemo da zaključimo o stanovnicima A i B?\<close>

lemma vitezovi: 
  assumes "k \<longleftrightarrow> (k \<longleftrightarrow> ans)"
  shows "ans"
  using assms
  by auto

definition bar_jedan:: "bool \<Rightarrow> bool \<Rightarrow> bool" 
  where "bar_jedan A B \<longleftrightarrow> A \<or> B"

lemma 
  assumes "kA \<longleftrightarrow> (\<not> kA \<or> \<not> kB)"
  shows "kA \<and> \<not> kB"
proof
  show "kA"
  proof (rule ccontr)
    assume "\<not> kA"
    then have "\<not>kA \<or> \<not>kB" by simp
    with assms have "kA" by simp 
    thus "False" using \<open>\<not>kA\<close>  by simp
  qed
  from assms \<open>kA\<close> have "\<not>kA \<or> \<not>kB" using assms by auto
  thus "\<not> kB" using \<open>kA\<close> by auto
qed

text \<open>Napisati detaljan dokaz u Isar-u.\<close>

text \<open>\<open>Napomena\<close>: Dozvoljeno je korišćenje samo \<open>simp\<close> metode za dokazivanje među koraka.\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle={Matematička indukcija}, points=6]\<close>

text \<open>Matematičkom indukcijom pokazati da važi:
      $$-3 + 3 + 9 + \ldots + (6n - 9) = 3n^2 - 6n.$$\<close>

text \<open>Primitivnom rekurzijom definisati funkciju \<open>suma :: nat \<Rightarrow> int\<close> 
      koja računa zadatu sumu, te indukcijom u Isar-u detaljno pokazati 
      da je ona ekvivalentna desnoj strani jednakosti.\<close>

fun suma:: "nat \<Rightarrow> int"
  where "suma 0 = 0"
  | "suma (Suc n) = suma n + (6 * int (Suc n) - 9)"

value "suma 1"

text \<open>\<open>Napomena\<close>: Dozvoljeno je korišćenje samo \<open>simp\<close> metode za dokazivanje među koraka.\<close>

text \<open>\<open>Savet\<close>: Formulisati, dokazati u Isar-u i iskoristiti pomocnu lemu koja opisuje
               narednu jednakost: $$3 \cdot Suc (n)^2 - 6 \cdot Suc (n) =  3 n^2 - 3.$$.\<close>

text \<open>\<open>Savet\<close>: Od dodatnih lema možete koristiti \<open>power2_sum\<close>, \<open>power2_eq_square\<close>, 
               i leme iz grupe \<open>algebra_simps\<close>. 
               Voditi računa o tipovima u pomoćnoj i glavnoj lemi.\<close>

lemma "suma n = (3 * int (n)^2 - 6 * (int n))"
proof (induction n)
  case 0
  then show ?case by (simp add: algebra_simps)
next
  case (Suc n)
  note IH = this
  have "suma (Suc n) = suma n + (6* int(Suc n) - 9)" by (simp add:algebra_simps)
  also have "... = (3 * int (n^2) - 6 * (int n)) + (6 * int (Suc n) - 9)" using IH by (simp add: algebra_simps)
  also have "... = 3 * int(n^2) - 6*(int n) + 6 * int (n+1) - 9" by (simp add: algebra_simps)
  also have "... = 3 * int(n^2) - 6*(int n) + 6 * int n + 6 - 9" by (simp add: algebra_simps)
  also have "... = 3 * int(n^2) - 3" by (simp add: algebra_simps)
  also have "... = 3 * (int(n^2) + 2 * int n + 1) - 6 * (int n + 1)" by (simp add: algebra_simps)
  also have "... = 3 * (int n + 1)^2 - 6 * (int n + 1)" by (simp add: algebra_simps power2_eq_square)
  also have "... = 3 * int(Suc n)^2 - 6 * int(Suc n)" by (simp add: algebra_simps)
  finally show ?case .
qed


text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
