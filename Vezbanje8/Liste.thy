theory Liste
  imports Main

begin

datatype 'a lista = 
  Prazna
  | Dodaj 'a "'a lista"

definition test:: "nat lista" where "test = Dodaj (1::nat) (Dodaj 2 (Dodaj 3 Prazna))"
definition test1:: "nat lista" where "test1 = Dodaj (5::nat) (Dodaj 7 (Dodaj 8 (Dodaj 10 Prazna)))"

fun duzina:: "'a lista \<Rightarrow> nat"
  where "duzina Prazna = 0"
  | "duzina (Dodaj x xs) = 1 + duzina xs"

value "duzina test"

fun nadovezi:: "'a lista \<Rightarrow> 'a lista \<Rightarrow> 'a lista"
  where "nadovezi Prazna ys = ys"
  | "nadovezi (Dodaj x xs) ys = Dodaj x (nadovezi xs ys)"

value "nadovezi test test1"

fun obrni:: "'a lista \<Rightarrow> 'a lista"
  where "obrni Prazna = Prazna"
  | "obrni (Dodaj x xs) = nadovezi (obrni xs) (Dodaj x Prazna)"

value "obrni test"

fun duzina':: "'a list \<Rightarrow> nat"
  where "duzina' [] = 0"
  | "duzina' (x#xs) = 1 + duzina' xs"

value "duzina' [5::nat, 10,15,20]"

fun prebroj:: "'a list \<Rightarrow> 'a \<Rightarrow> nat"
  where "prebroj [] b = 0"
  | "prebroj (x#xs) b = (if x = b then (1 + prebroj xs b) else (prebroj xs b))"

fun sadrzi:: " 'a list \<Rightarrow> 'a \<Rightarrow> bool"
  where "sadrzi [] a \<longleftrightarrow> False"
  | "sadrzi (x#xs) a \<longleftrightarrow> (x = a) \<or> (sadrzi xs a)"

value "sadrzi [2::nat, 4, 8, 10, 5] (5::nat)"

fun skup:: "'a list \<Rightarrow> 'a set"
  where "skup [] = {}"
  | "skup (x#xs) = {x} \<union> skup xs"

value "skup [1::nat,2,3,456,7]"

fun nadovezii:: "'a list \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "nadovezii [] ys = ys"
  | "nadovezii (x#xs) ys = [x] @ nadovezii xs ys"

value "nadovezii [1::nat, 3,5,7] [2::nat, 4,6,8]"

fun obrnii:: "'a list \<Rightarrow> 'a list"
  where "obrnii [] = []"
  | "obrnii (x#xs) = nadovezii (obrnii xs) [x]"

value "obrnii [2::nat, 4,6,7,9]"
s



end