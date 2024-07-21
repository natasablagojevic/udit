theory Cas8
  imports Main HOL.Real
begin 

(*
  1 - 2 + 3 - 4 + .. + 1999 - 2000



*)

value 
"let n = 2000 in (\<Sum> i = 1..n. (if i mod 2 \<noteq> 0 then int i else -(int i))) = 
   (if n mod 2 \<noteq> 0 then (n+1) div 2 else -(n div 2)) "

lemma 
  (*"(\<Sum> i = 1..n. i^2) = x"*)
  "(\<Sum> i = 1..n. (if i mod 2 \<noteq> 0 then int i else -(int i))) = 
   (if n mod 2 \<noteq> 0 then (n+1) div 2 else -(n div 2)) "
proof (induction n)
  case 0
  show ?case 
    by auto 

next 
  case (Suc n)
  let ?f = "(\<lambda> i. if i mod 2 \<noteq> 0 then i else -i)"
  show ?case 
  proof (cases "n mod 2 = 0")

    case True 
    then have "Suc n mod 2 \<noteq> 0" by auto

    have "(\<Sum> i = 1..Suc n. ?f i) = (\<Sum> i = 1..n. ?f i) + (?f (Suc n))"
      by simp 

    also have "... = (\<Sum> i = 1..n. ?f i) + (Suc n)"
      using \<open>Suc n mod 2 \<noteq> 0\<close>
      by simp

    also have "... =  - (int n div 2) + (Suc n)"
      using Suc \<open>n mod 2 = 0\<close>
      by simp 

    also have "... = (int n + 2) div 2"
      using \<open>n mod 2 = 0\<close>
      by auto 

    finally 
    show ?thesis 
      using \<open>Suc n mod 2 \<noteq> 0\<close>
      by simp
  next

    case False 
    show ?thesis
      sorry
    
  qed 
qed 


(*
  - ADT - algebraic data types
*)

datatype 'a  Lista = 
  Prazna 
  | Dodaj 'a "'a Lista" 

value "Prazna"
value "Dodaj (3::nat) Prazna"
value "Dodaj (5::int) (Dodaj 3 Prazna)"

definition test_lista :: "nat Lista" where 
  "test_lista = Dodaj 5 (Dodaj 3 Prazna)"


primrec duzina :: "'a Lista \<Rightarrow> nat" where 
  "duzina Prazna = 0" 
| "duzina (Dodaj x xs) = 1 + duzina xs"


value "duzina test_lista"

(*primrec zbir :: "('a::{zero, plus}) Lista \<Rightarrow> 'a" where*) 
primrec zbir :: "nat Lista \<Rightarrow> nat" where
  "zbir Prazna = 0"
| "zbir (Dodaj x xs) = x + zbir xs"

primrec dodaj_na_kraj :: "'a Lista \<Rightarrow> 'a  \<Rightarrow> 'a Lista" where 
  "dodaj_na_kraj Prazna y = Dodaj y Prazna"
| "dodaj_na_kraj (Dodaj x xs) y  = Dodaj x (dodaj_na_kraj xs y)" 

primrec spoj :: "'a Lista \<Rightarrow> 'a Lista \<Rightarrow> 'a Lista" where
  "spoj Prazna ys = ys"
| "spoj (Dodaj x xs) ys = Dodaj x (spoj xs ys)"


(*
- ako je nesto napisano rekurzivno, moze da se dokaze induktivno
- vrsis indukciju po onom prarametru po kom je rekurzija isla
- 
*)

thm spoj.simps(1)

lemma 
  "zbir (poj xs ys) = zbir xs + zbir ys"
proof (induction xs)

  case Prazna 
  show ?case 
    by simp

next 
  case (Dodaj x1 xs)
  show ?case 
    apply (subst spoj.simps(2))

qed

value "[1::nat, 2, 3, 4]"
value "Cons 3 [1::nat, 2, 3, 4]"
value "3 # [1::nat, 2, 3, 4]"
value "[1, 2, 3::nat] @ [4, 5, 6]"
value "[1::nat, 2, 3, 4] @ [5]"       (* O(n) operacija *)
value "sum_list [1::nat, 2, 3]"
value "length [1::nat, 2, 3]"         (* duzina liste  *)


primrec duzina :: "'a list \<Rightarrow> nat" where
  "duzina [] = 0"
| "duzina (x # xs) = 1 + duzina xs"

lemma "duzina (xs @ ys) = duzina xs + duzina ys"
  by (induction xs) auto


primrec obrni :: "'a Lista \<Rightarrow> 'a Lista" where 
  "obrni Prazna = Prazna"
| "obrni (Dodaj x xs) = spoj (obrni xs) (Dodaj x Prazna)"

lemma spojPrazna [simp]:
  shows "spoj xs Prazna = xs"
  apply (induction xs)
  by auto

lemma spojAsoc [simp]:
  "spoj (spoj xs ys) zs = spoj xs (spoj ys zs)"
  by (induction xs) auto

lemma "obrni (spoj xs ys) = spoj (obrni ys) (obrni xs)"
  apply (induction xs)
   apply simp
  by simp

end