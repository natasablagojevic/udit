
(*<*)
theory KLK
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
     apply assumption
    apply assumption
   apply (erule iffE)
   apply (erule impE)
    apply (erule impE)
     apply assumption+
   apply (erule iffE)
   apply (erule impE) back back
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
  (*<*) oops (*>*)

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

text \<open>Napisati detaljan dokaz u Isar-u.\<close>

definition vitez:: "bool \<Rightarrow> bool"
  where "vitez x \<equiv> x"

definition podanik:: "bool \<Rightarrow> bool"
  where "podanik x \<equiv> (\<not>x)"

lemma 
  assumes "vitez A \<or> podanik A"
  assumes "vitez B \<or> podanik B"
  assumes "A \<longrightarrow> (\<not>A \<or> \<not>B)"
  shows "podanik A"
proof (cases "A")
  assume "A"
  from this assms(3) have "\<not>A \<or> \<not>B" by auto
  then have "\<not>B" using \<open>A\<close> by auto

  show "podanik A"
    sorry

next 
  assume "\<not>A"
  show "podanik A"
    sorry

qed

text \<open>\<open>Napomena\<close>: Dozvoljeno je korišćenje samo \<open>simp\<close> metode za dokazivanje među koraka.\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle={Matematička indukcija}, points=6]\<close>

text \<open>Matematičkom indukcijom pokazati da važi:
      $$-3 + 3 + 9 + \ldots + (6n - 9) = 3n^2 - 6n.$$\<close>

text \<open>Primitivnom rekurzijom definisati funkciju \<open>suma :: nat \<Rightarrow> int\<close> 
      koja računa zadatu sumu, te indukcijom u Isar-u detaljno pokazati 
      da je ona ekvivalentna desnoj strani jednakosti.\<close>

text \<open>\<open>Napomena\<close>: Dozvoljeno je korišćenje samo \<open>simp\<close> metode za dokazivanje među koraka.\<close>

text \<open>\<open>Savet\<close>: Formulisati, dokazati u Isar-u i iskoristiti pomocnu lemu koja opisuje
               narednu jednakost: $$3 \cdot Suc (n)^2 - 6 \cdot Suc (n) =  3 n^2 - 3.$$.\<close>

(*
3 (n+1)^2 - 6(n+1) = 3n^2 + 6n + 3 - 6n - 6 = 3n^2 - 3
*)

text \<open>\<open>Savet\<close>: Od dodatnih lema možete koristiti \<open>power2_sum\<close>, \<open>power2_eq_square\<close>, 
               i leme iz grupe \<open>algebra_simps\<close>. 
               Voditi računa o tipovima u pomoćnoj i glavnoj lemi.\<close>

primrec suma:: "nat \<Rightarrow> nat"
  where "suma 0 = 0"
  | "suma (Suc n) = suma n + (6*(Suc n) - 9)"

lemma "suma n = 3*(n^2) - 6*n"
proof (induction n)
  case 0
  then show ?case by auto
next
  case (Suc n)
  note IH = this

  have "suma (Suc n) = suma n + (6 * (Suc n) - 9)" by (simp add: algebra_simps)
  also have "... = 3*(n^2) - 6*n + (6*(n+1) - 9)" using IH by (simp add: algebra_simps)
  also have "... = 3*(n^2) - 6*n + (6*n +6 - 9) " by (simp add: algebra_simps)
  also have "... = 3*(n^2) - 6*n + (6*n - 3)" by (simp add: algebra_simps)
  also have "... = 3*(n^2) - 3" by (simp add: algebra_simps)
  also have "... = 3*((n+1)^2) - 6*(n+1)" 
    by (smt (verit, del_insts) add.commute add_diff_cancel_right add_mult_distrib add_mult_distrib2 mult_2 mult_numeral_1_right numeral_Bit0_eq_double numerals(1) one_power2 power2_sum)
 also have "... = 3*(Suc n)^2 - 6* (Suc n)" by (simp add: algebra_simps)
  finally show ?case .
qed


text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
