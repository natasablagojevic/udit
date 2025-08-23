theory Drveta
  imports Main

begin

datatype t3 = 
  List 
  | Cvor t3 t3 t3

fun br_list:: "t3 \<Rightarrow> nat"
  where "br_list List = 1"
  | "br_list (Cvor l s d) = br_list l + br_list s + br_list d"

fun br_cvor:: "t3 \<Rightarrow> nat"
  where "br_cvor List = 0"
  | "br_cvor (Cvor l s d) = 1 + br_cvor l + br_cvor s + br_cvor d"

(*
lemma 
  shows "\<exists>a b. br_list t = a * br_cvor t + b"
  by (intro exI[of _ 2] exI[of _ 1], induction t) simp
*)

lemma "br_list t = 2 * br_cvor t + 1"
  by (induction t) auto 


datatype 'a drvo = 
  List 
  | Cvor "'a drvo" 'a "'a drvo"

definition test:: "nat drvo" where "test = Cvor (Cvor (Cvor List 1 List) 5 (Cvor (Cvor List 2 List) 3 (Cvor List 4 List))) 6 (Cvor (Cvor List 7 List) 8 (Cvor List 9 List))"

fun zbir:: "nat drvo \<Rightarrow> nat"
  where "zbir List = 0"
  | "zbir (Cvor levo x desno) = x + zbir levo + zbir desno"

value "zbir test"

fun visina:: "'a drvo \<Rightarrow> nat"
  where "visina List = 0"
  | "visina (Cvor levo x desno) = 1 + (max (visina levo) (visina desno))"

value "visina test"


fun pronadji:: "nat drvo \<Rightarrow> nat \<Rightarrow> bool"
  where "pronadji List a \<longleftrightarrow> False"
  | "pronadji (Cvor levo x desno) a \<longleftrightarrow> (pronadji levo a) \<or> x = a \<or> (pronadji desno a)"

(** --- ako se radi o binarno pretrazivackom stablu ---  **)

fun pronadji_najveci_element:: "nat drvo \<Rightarrow> nat"
  where "pronadji_najveci_element List = 0"
  | "pronadji_najveci_element (Cvor List x List) = x"
  | "pronadji_najveci_element (Cvor levo x desno) = pronadji_najveci_element desno"

value "pronadji_najveci_element test"

fun pronadji_najmanji_element:: "nat drvo \<Rightarrow> nat"
  where "pronadji_najmanji_element List = 0"
  | "pronadji_najmanji_element (Cvor List x List) = x"
  | "pronadji_najmanji_element (Cvor levo x desno) = pronadji_najmanji_element levo" 

value "pronadji_najmanji_element test"


fun elementi_na_i_nivou:: "nat drvo \<Rightarrow> nat \<Rightarrow> nat list"
  where "elementi_na_i_nivou  List 0 = []"
  | "elementi_na_i_nivou (Cvor levo x desno) 0 = [x]"
  | "elementi_na_i_nivou List (Suc i) = []"
  | "elementi_na_i_nivou (Cvor levo x desno) (Suc i) = elementi_na_i_nivou levo i @ elementi_na_i_nivou desno i"

value "elementi_na_i_nivou test 2"


fun broj_cvorova_na_i_nivou:: "nat drvo \<Rightarrow> nat  \<Rightarrow> nat"
  where "broj_cvorova_na_i_nivou List 0  = 0"
  | "broj_cvorova_na_i_nivou (Cvor levo x desno) 0 = 1"
  | "broj_cvorova_na_i_nivou List (Suc i) = 0"
  | "broj_cvorova_na_i_nivou (Cvor levo x desno) (Suc i) = broj_cvorova_na_i_nivou levo i + broj_cvorova_na_i_nivou desno i"

value "broj_cvorova_na_i_nivou test 3"

fun broj_cvorova:: "nat drvo \<Rightarrow> nat"
  where "broj_cvorova List = 0"
  | "broj_cvorova (Cvor levo x desno) = 1 + broj_cvorova levo + broj_cvorova desno"

value "broj_cvorova test"

fun broj_unutrasnjih_cvorova:: "nat drvo \<Rightarrow> nat"
  where "broj_unutrasnjih_cvorova List = 0"
  | "broj_unutrasnjih_cvorova (Cvor List x List) = 0"
  | "broj_unutrasnjih_cvorova (Cvor levo x desno) = 1 + broj_unutrasnjih_cvorova levo + broj_unutrasnjih_cvorova desno"

value "broj_unutrasnjih_cvorova test"

fun broj_listova:: "nat drvo \<Rightarrow> nat"
  where "broj_listova List = 1"
  | "broj_listova (Cvor List x List) = 1"
  | "broj_listova (Cvor levo x desno) = broj_listova levo + broj_listova desno"

value "broj_listova test"

fun ispisi_listove:: "nat drvo \<Rightarrow> nat list"
  where "ispisi_listove List = []"
  | "ispisi_listove (Cvor List x List) = [x]"
  | "ispisi_listove (Cvor levo x desno) = ispisi_listove levo  @ ispisi_listove desno"

value "ispisi_listove test"

fun ispisi_unutrasnje_cvorove:: "nat drvo \<Rightarrow> nat list"
  where "ispisi_unutrasnje_cvorove List = []"
  | "ispisi_unutrasnje_cvorove (Cvor List x List) = []"
  | "ispisi_unutrasnje_cvorove (Cvor levo x desno) = ispisi_unutrasnje_cvorove levo @ [x] @ ispisi_unutrasnje_cvorove desno"

value "ispisi_unutrasnje_cvorove test"

fun skup:: "nat drvo \<Rightarrow> nat set"
  where "skup List = {}"
  | "skup (Cvor levo x desno) = skup levo \<union> {x} \<union> skup desno"

value "skup test"

fun je_binarno:: "nat drvo \<Rightarrow> bool"
  where "je_binarno List \<longleftrightarrow> True"
  | "je_binarno (Cvor levo x desno) \<longleftrightarrow> (\<forall>a \<in> skup levo. a \<le> x) \<and> (\<forall>a \<in> skup desno. a > x) \<and> (je_binarno levo) \<and> (je_binarno desno)"

definition test1:: "nat drvo" where "test1 = Cvor (Cvor (Cvor List 1 List) 2 (List)) 7 (Cvor (List) 9 (Cvor (Cvor List 18 List) 32 (List)))"

value "je_binarno test"
value "je_binarno test1"

fun infiks:: "nat drvo \<Rightarrow> nat list"
  where "infiks List = []"
  | "infiks (Cvor levo x desno) = infiks levo @ [x] @ infiks desno"

fun prefiks:: "nat drvo \<Rightarrow> nat list"
  where "prefiks List = []"
  | "prefiks (Cvor levo x desno) = [x] @ prefiks levo @ prefiks desno"

fun postfiks:: "nat drvo \<Rightarrow> nat list"
  where "postfiks List = []"
  | "postfiks (Cvor levo x desno) = postfiks levo @ postfiks desno @ [x]"

value "infiks test1"

fun ubaci_cvor:: "nat drvo \<Rightarrow> nat \<Rightarrow> nat drvo"
  where "ubaci_cvor List a = Cvor List a List"
  | "ubaci_cvor (Cvor levo x desno) a = (if (a \<le> x) then Cvor (ubaci_cvor levo a) x desno else Cvor levo x (ubaci_cvor desno a))"

value "infiks (ubaci_cvor test1 17)"

fun gen_kompletno:: "nat \<Rightarrow> nat drvo"
  where "gen_kompletno 0 = List"
  | "gen_kompletno (Suc n) = Cvor (gen_kompletno n) 1 (gen_kompletno n)"

value "gen_kompletno 2"

(* ---------------------------------------------------------------------------------------------  *)





end