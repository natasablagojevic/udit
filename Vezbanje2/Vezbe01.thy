
(*<*)
theory Vezbe01
  imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Primer jednostavne teorije]\<close>

text \<open>(a) Pokazati da važi komutativnost i asocijativnost 
          operacije @{text "(+) :: nat \<Rightarrow> nat \<Rightarrow> nat"}.\<close>

lemma "(a::nat) + b = b + a"
  by auto 

lemma "((a::nat) + b) + c = a + (b + c)"
  by auto 

text \<open>(b) Definisati funkciju @{text "sledbenik :: nat \<Rightarrow> nat"} i 
          pokazati da važi @{text "sledbenik (sledbenik x) = x + 2"}.\<close>

definition sledbenik:: "nat \<Rightarrow> nat" 
  where "sledbenik x = x + 1"

text \<open>(c) Pokazati da ako važi @{text "x > 0"} onda @{text "sledbenik x > 1"}.
          Te pokazati da ako važi @{text "x < 5"} onda @{text "sledbenik x < 6"}.\<close>

lemma "x > 0 \<longrightarrow> sledbenik x > 1"
  unfolding sledbenik_def
  by auto 

lemma "x < 5 \<longrightarrow> sledbenik x < 6"
  unfolding sledbenik_def
  by auto 

text \<open>(d) Prethodna dva tvrđenja uopštiti u opšte tvrđenje o ograničenosti sledbenika.\<close>

lemma 
  fixes a b::nat 
  assumes "a < x" "x < b"
  shows "a+1 < sledbenik x \<and> sledbenik x < b + 1"
  unfolding sledbenik_def 
  using assms
  by auto 

text \<open>(e) Definisati funkciju @{text "kvadrat :: nat \<Rightarrow> nat"} i
          pokazati da važi @{text "kvadrat (x + 1) = kvadrat x + 2 * x + 1"}.\<close>

definition kvadrat:: "nat \<Rightarrow> nat"
  where "kvadrat x = x*x"

lemma "kvadrat (x + 1) = kvadrat x + 2 * x + 1"
  unfolding kvadrat_def
  by auto 

text \<open>(f) Definisati rekurzivnu funkciju @{text "sum :: nat list \<Rightarrow> nat"} koja računa sumu 
          liste prirodnih brojeva. Pokazati da se @{text "sum xs"} ponaša isto kao 
          i @{text "foldr"} primenjen na odgovarajuću funkciju, listu @{text "xs"}, i 
          odgovarajuću početnu vrenodst akomulatora. Nako toga pokazati sledeće svojstvo 
          @{text "sum (xs @ ys) = sum xs + sum ys"}.\<close>

fun sum:: "nat list \<Rightarrow> nat"
  where "sum [] = 0"
  | "sum (x#xs) = x + sum xs"

value "sum [1,2,3]"

text \<open>(g) Definisati rekurzivnu funkciju @{text "len :: nat list \<Rightarrow> nat"} koja računa dužinu 
          liste prirodnih brojeva. Pokazati da se @{text "len xs"} ponaša isto kao 
          i @{text "foldr"} primenjen na odgovarajuću funkciju, listu @{text "xs"}, i
          odgovarajuću početnu vrednost akumulatora (Savet: Zgodno je koristiti 
          lambda funkciju @{text "(\<lambda> x y. f x y)"} za definisanje funkcije koju prima
          @{text "foldr"}). Nako toga pokazati sledeće svojstvo 
          @{text "len (xs @ ys) = len xs + len ys"}.\<close>

fun len:: "nat list \<Rightarrow> nat"
  where "len [] = 0"
  | "len (x#xs) = 1 + len xs" 

value "len [1,10,100]"

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Zapisivanje logičkih formula]\<close> 

text \<open>(a) Zapisati nekoliko logičkih formula koje uključuju 
          logičke konstante @{text "True"} i @{text "False"},
          logičke veznike @{text "\<not>"}, @{text "\<and>"}, @{text "\<or>"}, 
          @{text "\<longrightarrow>"}, i @{text "\<longleftrightarrow>"}/@{text "="}, i
          univerzalne i egzistencionalne kvantifikatore @{text "\<forall>"} i @{text "\<exists>"}\<close>

text \<open>(b) Zapisati sledeće rečenice u logici prvog reda i dokazati njihovu ispravnost.\<close>

text \<open>(b.1) Ako onaj ko laže taj i krade i ako bar neko laže, onda neko i krade.\<close>

(*

laze(x) = x laze 
krade(x) = x krade 

\<forall>x. laze x \<longrightarrow> krade x 
\<exists>x. laze x 
\<longrightarrow> \<exists>x. krade x 

*)

lemma "(\<forall>x. laze x \<longrightarrow> krade x) \<and> (\<exists>x. laze x) \<longrightarrow> (\<exists>x. krade x)"
  by auto 

text \<open>(b.2) Ako ”ko radi taj ima ili troši” i ”ko ima taj peva” i ”ko troši taj peva”, onda
”ko radi taj peva”\<close>

(*

radi(x) = x radi 
ima(x) = x ima 
trosi(x) = x trosi 
peva(x) = x peva 

\<forall>x. radi x \<longrightarrow> ima x \<or> trosi x 
\<forall>x. ima x \<longrightarrow> peva x 
\<forall>x. trosi x \<longrightarrow> peva x 
\<longrightarrow> \<forall>x. radi x \<longrightarrow> peva x 

*)

lemma "(\<forall>x. radi x \<longrightarrow> ima x \<or> trosi x) \<and> (\<forall>x. ima x \<longrightarrow> peva x) \<and> (\<forall>x. trosi x \<longrightarrow> peva x) \<longrightarrow> (\<forall>x. radi x \<longrightarrow> peva x)"
  by auto 

text \<open>(c) Zapisati sledeći skup rečenica u logici prvog reda i dokazati njihovu 
          nezadovoljivost.\<close>

text \<open>(c.1) Ako je X prijatelj osobe Y, onda je i Y prijatelj osobe X.\<close>
text \<open>(c.2) Ako je X prijatelj osobe Y, onda X voli Y.\<close>
text \<open>(c.3) Ne postoji neko ko je povredio osobu koju voli.\<close>
text \<open>(c.4) Osoba Y je povredila svog prijatelja X.\<close>

(*

prijatelj(x, y) = x je prijatelj od y
voli(x, y) = x voli y 
povredio(x, y) = x je povredio y


\<forall>x y. prijatelj x y \<longrightarrow> prijatelj y x 
\<forall>x y. prijatelj x y \<longrightarrow> voli x y 
\<not>(\<exists>x y. povredio x y \<and> voli x y)
\<exists>y x. povredio y x \<and> prijatelj y x 

*)

lemma "(\<forall>x y. prijatelj x y \<longrightarrow> prijatelj y x) \<and> (\<forall>x y. prijatelj x y \<longrightarrow> voli x y) \<and> (\<not>(\<exists>x y. povredio x y \<and> voli x y)) \<and> (\<exists>y x. povredio y x \<and> prijatelj y x) \<longrightarrow> False"
  by auto 

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
