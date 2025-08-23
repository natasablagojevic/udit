theory Lista
  imports Main


begin

datatype 'a lista =
  Prazna 
  | Dodaj 'a "'a lista"

definition test:: "nat lista" where "test = Dodaj 1 (Dodaj 15 (Dodaj 8 (Dodaj 14 Prazna)))"

value "test"

fun print_list:: "nat lista \<Rightarrow> nat list"
  where "print_list Prazna = []"
  | "print_list (Dodaj x xs) = [x] @ print_list xs"

value "print_list test"

fun list_size:: "nat lista \<Rightarrow> nat"
  where "list_size Prazna = 0"
  | "list_size (Dodaj x xs) = 1 + list_size xs"

value "list_size test"

fun find:: "nat lista \<Rightarrow> nat \<Rightarrow> bool" 
  where "find Prazna a \<longleftrightarrow> False"
  | "find (Dodaj x xs) a \<longleftrightarrow> (x = a) \<or> (find xs a)"

value "find test 8"

fun sum:: "nat lista \<Rightarrow> nat"
  where "sum Prazna = 0"
  | "sum (Dodaj x xs) = x + sum xs"

value "sum test"

fun add_node:: "nat lista \<Rightarrow> nat \<Rightarrow> nat lista"
  where "add_node Prazna a = Dodaj a Prazna"
  | "add_node (Dodaj x xs) a = Dodaj x (add_node xs a)"

value "add_node test 16"








end