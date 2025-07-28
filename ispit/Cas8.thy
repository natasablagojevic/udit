theory Cas8  
  imports Main

begin 

value "[1..<5]"

value "sum_list [1..<5]"

datatype 'a lista = Prazna 
  | Dodaj 'a "'a lista"


term "Dodaj (1::nat) (Dodaj 2 (Dodaj 3 Prazna))"

fun duzina:: "'a lista \<Rightarrow> nat" 
  where "duzina Prazna = 0"
  | "duzina (Dodaj x xs) = (1::nat) + duzina xs"

fun nadovezi:: "'a lista \<Rightarrow> 'a lista \<Rightarrow> 'a lista"
  where "nadovezi Prazna ys = ys" 
  | "nadovezi (Dodaj x xs) ys = Dodaj x (nadovezi xs ys)"

primrec prebroj:: "('a::equal) \<Rightarrow> 'a list \<Rightarrow> nat"
  where "prebroj a [] = 0"
  | "prebroj a (x#xs) = (if x = a then 1 + prebroj a xs else prebroj a xs)"


primrec sadrzi:: "('a::equal) \<Rightarrow> 'a list \<Rightarrow> bool"
  where "sadrzi a [] \<longleftrightarrow> False"
  | "sadrzi a (x#xs) \<longleftrightarrow> a = x \<or> (sadrzi a xs)"

primrec skup:: "'a list \<Rightarrow> 'a set"
  where "skup [] = {}"
  | "skup (x#xs) = {x} \<union> (skup xs)"


end