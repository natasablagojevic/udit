theory Stabla
  imports Main

begin

datatype 'a drvo = 
  List 
  | Cvor "'a drvo" 'a "'a drvo"

definition test::"nat drvo" where "test = Cvor (Cvor (Cvor List 3 List) 7 (Cvor (Cvor List 8 List) 10 (Cvor List 12 List))) 15 (Cvor (Cvor List 20 List) 25 (Cvor List 30 List))"

value "test"

fun ubaci_cvor:: "nat \<Rightarrow> nat drvo \<Rightarrow> nat drvo"
  where "ubaci_cvor a List = Cvor List a List"
  | "ubaci_cvor a (Cvor levo x desno) = (if (a \<le> x) then (Cvor (ubaci_cvor a levo) x desno) else (Cvor levo x (ubaci_cvor a desno)))"

value "ubaci_cvor 1 test"

fun visina:: "nat drvo \<Rightarrow> nat"
  where "visina List = 0"
  | "visina (Cvor levo x desno) = 1 + max (visina levo) (visina desno)"

value "visina test"

fun find:: "nat \<Rightarrow> nat drvo \<Rightarrow> bool"
  where "find a List \<longleftrightarrow> False"
  | "find a (Cvor levo x desno) \<longleftrightarrow> (find a levo) \<or> (find a desno) \<or> (x = a)"

value "find 58  test"

fun najveci_element:: "nat drvo \<Rightarrow> nat"
  where "najveci_element List = 0"
  | "najveci_element (Cvor List x List) = x"
  | "najveci_element (Cvor levo x desno) = najveci_element desno"

value "najveci_element test"

fun najmanji_element:: "nat drvo \<Rightarrow> nat"
  where "najmanji_element List = 0"
  | "najmanji_element (Cvor List x List) = x"
  | "najmanji_element (Cvor levo x desno) = najmanji_element levo"

value "najmanji_element test"


(* broj svih cvorova u stablu *)
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

fun elementi_na_i_nivou:: "nat drvo \<Rightarrow> nat \<Rightarrow> nat list"
  where "elementi_na_i_nivou List _ = []"
  | "elementi_na_i_nivou (Cvor levo x desno) 0 = [x]"
  | "elementi_na_i_nivou (Cvor levo x desno) (Suc i) = elementi_na_i_nivou levo i @ elementi_na_i_nivou desno i"

value "elementi_na_i_nivou test 2"


fun broj_elemenata_na_i_nivou:: "nat drvo \<Rightarrow> nat \<Rightarrow> nat"
  where "broj_elemenata_na_i_nivou List _ = 0"
  | "broj_elemenata_na_i_nivou (Cvor levo x desno) 0 = 1"
  | "broj_elemenata_na_i_nivou (Cvor levo x desno) (Suc i) = broj_elemenata_na_i_nivou levo i + broj_elemenata_na_i_nivou desno i"

value "broj_elemenata_na_i_nivou test 2"

fun suma:: "nat drvo \<Rightarrow> nat"
  where "suma List = 0"
  | "suma (Cvor levo x desno) = x + suma levo + suma desno"

value "suma test"

fun ispisi_listove:: "nat drvo \<Rightarrow> nat list"
  where "ispisi_listove List = []"
  | "ispisi_listove (Cvor List x List) = [x]"
  | "ispisi_listove (Cvor levo x desno) = ispisi_listove levo @ ispisi_listove desno"

value "ispisi_listove test"


fun ispisi_unutrasnje:: "nat drvo \<Rightarrow> nat list"
  where "ispisi_unutrasnje List = []"
  | "ispisi_unutrasnje (Cvor List x List) = []"
  | "ispisi_unutrasnje (Cvor levo x desno) = ispisi_unutrasnje levo @ [x] @ ispisi_unutrasnje desno"

value "ispisi_unutrasnje test"




end