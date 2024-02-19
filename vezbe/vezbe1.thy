
(*<*)
theory Vezbe01
  imports Main
begin
(*>*)

text_raw ‹\begin{exercise}[subtitle=Primer jednostavne teorije]›

text ‹(a) Pokazati da važi komutativnost i asocijativnost 
          operacije @{text "(+) :: nat ⇒ nat ⇒ nat"}.›


theorem "(a:: nat) + b = b + a" 
  by simp 

theorem "((a:: nat) + b) + c = a + (b+c) "
  by simp

theorem "(a:: nat) + (b + c) = (a + b) + c"
  by simp


text ‹(b) Definisati funkciju @{text "sledbenik :: nat ⇒ nat"} i 
          pokazati da važi @{text "sledbenik (sledbenik x) = x + 2"}.›

definition sledbenik:: "nat ⇒ nat" where 
  "sledbenik x  = x + 1"

theorem "sledbenik (sledbenik x) = x + 2"
  unfolding sledbenik_def
  by simp

text ‹(c) Pokazati da ako važi @{text "x > 0"} onda @{text "sledbenik x > 1"}.
          Te pokazati da ako važi @{text "x < 5"} onda @{text "sledbenik x < 6"}.›

theorem "x > 0 ⟶ sledbenik x > 1" 
  unfolding sledbenik_def
  by simp

theorem "x < 5 ⟶ sledbenik x < 6"
  unfolding sledbenik_def
  by auto 

text ‹(d) Prethodna dva tvrđenja uopštiti u opšte tvrđenje o ograničenosti sledbenika.›

theorem "x > a ∧ x < b ⟶ sledbenik x > a+1 ∧ sledbenik x < b+1"
  unfolding sledbenik_def 
  by auto 

lemma 
  assumes "x > a" "x < b"
  shows "sledbenik x > a +1" "sledbenik x < b+1" 
  using assms
  unfolding sledbenik_def
  by auto 

text ‹(e) Definisati funkciju @{text "kvadrat :: nat ⇒ nat"} i
          pokazati da važi @{text "kvadrat (x + 1) = kvadrat x + 2 * x + 1"}.›

definition kvadrat:: "nat ⇒ nat" where "kvadrat x = x*x"

theorem "kvadrat (x + 1) = kvadrat x + 2 * x + 1"
  unfolding kvadrat_def
  by auto

text ‹(f) Definisati rekurzivnu funkciju @{text "sum :: nat list ⇒ nat"} koja računa sumu 
          liste prirodnih brojeva. Pokazati da se @{text "sum xs"} ponaša isto kao 
          i @{text "foldr"} primenjen na odgovarajuću funkciju, listu @{text "xs"}, i 
          odgovarajuću početnu vrenodst akomulatora. Nako toga pokazati sledeće svojstvo 
          @{text "sum (xs @ ys) = sum xs + sum ys"}.›

fun sum :: "nat list ⇒ nat" where "sum [] = 0"
  | "sum (x # xs) = x + sum xs" 

 
term "foldr"
lemma "sum xs = foldr (+) xs 0"
  apply (induction xs)
  by auto

theorem "sum (xs @ ys) = sum xs + sum ys" 
  apply (induction(xs))
  by auto 

text ‹(g) Definisati rekurzivnu funkciju @{text "len :: nat list ⇒ nat"} koja računa dužinu 
          liste prirodnih brojeva. Pokazati da se @{text "len xs"} ponaša isto kao 
          i @{text "foldr"} primenjen na odgovarajuću funkciju, listu @{text "xs"}, i
          odgovarajuću početnu vrednost akumulatora (Savet: Zgodno je koristiti 
          lambda funkciju @{text "(λ x y. f x y)"} za definisanje funkcije koju prima
          @{text "foldr"}). Nako toga pokazati sledeće svojstvo 
          @{text "len (xs @ ys) = len xs + len ys"}.›

fun len :: "nat list ⇒ nat" where
  "len [] = 0"
| "len (x#xs) = 1 + len xs"

term foldr

theorem "len xs = foldr (λ x y. 1 + y ) xs 0"
  apply (induction xs)
  by auto 

theorem "len (xs @ ys) = len xs + len ys"
  apply (induction xs)
  by auto 


text_raw ‹\end{exercise}›

text_raw ‹\begin{exercise}[subtitle=Zapisivanje logičkih formula]› 





text ‹(a) Zapisati nekoliko logičkih formula koje uključuju 
          logičke konstante @{text "True"} i @{text "False"},
          logičke veznike @{text "¬"}, @{text "∧"}, @{text "∨"}, 
          @{text "⟶"}, i @{text "⟷"}/@{text "="}, i
          univerzalne i egzistencionalne kvantifikatore @{text "∀"} i @{text "∃"}›

lemma "p ∧ q ⟶ q ∨ p "
  by auto 

(* demorgan *)
lemma "¬ (A ∧ B ) ⟶ ¬ A ∨ ¬B"
  by auto 

lemma "¬ (A ∨ B ) ⟶ ¬ A ∧ ¬B"
  by auto 

lemma "(¬ (¬ A)) ⟶  A"
  by auto 

lemma "(A ⟶ B) ⟶ ¬A ∨ B "
  by auto 

lemma "(∀x y. laze x ⟶ krade x) ∧ (∃ x. laze x) ⟶ (∃ x. krade x) "
  by auto 
 
text ‹(b) Zapisati sledeće rečenice u logici prvog reda i dokazati njihovu ispravnost.›

text ‹(b.1) Ako onaj ko laže taj i krade i ako bar neko laže, onda neko i krade.›

lemma "(∀x. laze x ⟶ krade x) ∧ (∃ x. laze x) ⟶ (∃ x. krade x) "
  by auto 
 

text ‹(b.2) Ako ”ko radi taj ima ili troši” i ”ko ima taj peva” i ”ko troši taj peva”, onda
”ko radi taj peva”›
(*
radi x 
trosi x
ima x

radi x ⇒ ima or trosi 
ima ⇒ peva 
trosi → peva 
-----------
radi → peva 
*)

lemma "(∀ x. radi x ⟶ ima x ∨ trosi x ) ∧ (∀ x. ima x ⟶ peva x) ∧ (∀ x. trosi x ⟶ peva x) ⟶ (∀x. radi x ⟶  peva x) "
  by auto 


text ‹(c) Zapisati sledeći skup rečenica u logici prvog reda i dokazati njihovu 
          nezadovoljivost.›

text ‹(c.1) Ako je X prijatelj osobe Y, onda je i Y prijatelj osobe X.›
text ‹(c.2) Ako je X prijatelj osobe Y, onda X voli Y.›
text ‹(c.3) Ne postoji neko ko je povredio osobu koju voli.›
text ‹(c.4) Osoba Y je povredila svog prijatelja X.›

(* nezadovoljivost ⇒ p1 and p2 and ... and pn = false  *)

(*
prijatelj x y  → prijatelj y x 
prijatelj x y → voli x y 

not exist x (exists y povredio x i voli x y )
*)

lemma "(∀ x y. prijatelj x y ⟶ prijatelj y  x)
   ∧ (∀ x y. prijatelj x y ⟶ voli x y)
   ∧ (¬(∃ x y. voli x y ∧ povredio x y ))
   ∧ (∃ x y. prijatelj x y ∧ povredio y x)
    --> False"
  by auto 


text_raw ‹\end{exercise}›

(*<*)
end
(*>*)
