theory sep1
  imports Main

begin

type_synonym vec3 = "int \<times> int \<times> int"

definition v1:: "vec3" 
  where "v1 \<equiv> (-1, 3, -1)"

definition v2:: "vec3"
  where "v2 \<equiv> (1, 2, 5)"

definition v3:: "vec3"
  where "v3 \<equiv> (4, 6, 7)"

definition C:: "int"
  where "C \<equiv> 5"

value "add v1 v2 = (0,5,4)"
value "sub v1 v2 = (-2,1,-6)"
value "mult 2 v1 = (-2, 6, -2)"
value "inter_product v1 v2 = 0"

fun add:: "vec3 \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "add (a1,b1,c1) (a2,b2,c2) = (a1+a2, b1+b2, c1+c2)"

fun sub:: "vec3 \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "sub (a1,b1,c1) (a2,b2,c2) = (a1-a2, b1-b2, c1-c2)"

fun mult:: "int \<Rightarrow> vec3 \<Rightarrow> vec3"
  where "mult d (a,b,c) = (a*d, b*d, c*d)"

fun inter_product :: "vec3 \<Rightarrow> vec3 \<Rightarrow> int"
  where "inter_product (a1,b1,c1) (a2,b2,c2) = a1*a2 + b1*b2 + c1*c2"

lemma "inter_product v1 v1 \<ge> 0"
  unfolding v1_def 
  by auto 

lemma "inter_product (add v1 v2) v3 = (inter_product v1 v3) + (inter_product v2 v3)"
  unfolding v1_def v2_def v3_def
  by auto 

lemma "inter_product (mult C v3) v2 = C * (inter_product v3 v2)"
  unfolding C_def v3_def v2_def 
  by auto

lemma "inter_product v1 (add v2 v3) = (inter_product v1 v2) + (inter_product v1 v3)"
  unfolding v1_def v2_def v3_def
  by auto 

lemma "inter_product v1 (mult C v3) = C * (inter_product v1 v3)"
  unfolding v1_def v3_def C_def 
  by auto 

definition orthogonal:: "vec3 \<Rightarrow> vec3 \<Rightarrow> bool"
  where "orthogonal x y \<longleftrightarrow> (inter_product x y = 0)"

fun norma:: "vec3 \<Rightarrow> int"
  where "norma v = inter_product v v "

lemma 
  fixes u v:: vec3
  assumes "othrogonal u v"
  shows "norma (add u v) = (norma u) + (norma v)"
proof - 
  have "norma (add u v) = inter_product (add u v) (add u v)" by simp 
  also have "... = (inter_product u u) + 2 * (inter_product u v) + (inter_product v v)" sorry
  also have "... = (inter_product u u) + (inter_product v v)" using assms unfolding orthogonal_def sorry
  also have "... = norma u + norma v" by auto 
  finally show ?thesis .
qed

(* ------------------------------------------------------------------------------------------------------------ *)

datatype 'a drvo = List 
  | Cvor "'a drvo" 'a "'a drvo"

definition test_drvo:: "nat drvo"
  where "test_drvo \<equiv> Cvor (Cvor (Cvor List 1 List) 5 (Cvor (Cvor List 2 List) 3 (Cvor List 4 List))) 6 (Cvor (Cvor List 7 List) 8 (Cvor List 9 List))"

fun broj_listova:: "'a drvo \<Rightarrow> nat"
  where "broj_listova List = 0"
  | "broj_listova (Cvor List _ List) = 1"
  | "broj_listova (Cvor levo x desno) = broj_listova levo + broj_listova desno"

value "broj_listova test_drvo"

fun dubina_stabla:: "'a drvo \<Rightarrow> nat"
  where "dubina_stabla List = 0"
  | "dubina_stabla (Cvor levo x desno) = 1 + (max (dubina_stabla levo) (dubina_stabla desno))" 

value "dubina_stabla test_drvo"

fun complete_tree:: "nat \<Rightarrow> nat drvo"
  where "complete_tree 0  = List"
  | "complete_tree (Suc n) = Cvor (complete_tree (n-1 div 2)) 1 (complete_tree (n-1 div 2))"

value "complete_tree 3"


fun is_complete:: "('a drvo \<Rightarrow> 'a) \<Rightarrow> 'a drvo \<Rightarrow> bool"
  where "is_complete f List \<longleftrightarrow> True"
  | "is_complete f (Cvor levo x desno) \<longleftrightarrow> (is_complete f levo) \<and> (is_complete f desno) \<and> (f levo = f desno)"

lemma "is_complete dubina_stabla t = is_complete broj_listova t"
  by (induction t) (auto simp add: is_complete.simps dubina_stabla.simps broj_listova.simps) 


(*----------------------------------------------------*)


fun pozitivni_listovi :: "int drvo \<Rightarrow> int list"
  where
    "pozitivni_listovi List = []"  (* Ako je stablo prazno, nema listova *)
  | "pozitivni_listovi (Cvor List x List) = (if x > 0 then [x] else [])"  (* Ako je čvor list i vrednost je pozitivna, dodajemo ga u rezultat *)
  | "pozitivni_listovi (Cvor levo _ desno) = pozitivni_listovi levo @ pozitivni_listovi desno"  (* Rekurzivno pretražujemo levo i desno podstablo *)


fun najveci_element :: "int drvo \<Rightarrow> int"
  where
    "najveci_element List = 0"  (* Ako je stablo prazno, vraćamo 0 *)
  | "najveci_element (Cvor _ x List) = x"  (* Ako nema desnog podstabla, vraćamo trenutni čvor *)
  | "najveci_element (Cvor _ _ desno) = najveci_element desno"  (* Inače, pretražujemo desno podstablo *)



fun broj_cvorova_na_nivou_i :: "'a drvo \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "broj_cvorova_na_nivou_i List _ _ = 0"  (* Ako je stablo prazno, nema čvorova *)
  | "broj_cvorova_na_nivou_i (Cvor levo _ desno) i trenutni_nivo =
       (if trenutni_nivo = i then 1 else 0) + 
       broj_cvorova_na_nivou_i levo i (trenutni_nivo + 1) + 
       broj_cvorova_na_nivou_i desno i (trenutni_nivo + 1)"


fun svi_na_nivou_i :: "'a drvo \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list"
  where
    "svi_na_nivou_i List _ _ = []"
  | "svi_na_nivou_i (Cvor levo x desno) i trenutni_nivo =
       svi_na_nivou_i levo i (trenutni_nivo + 1) @
       svi_na_nivou_i desno i (trenutni_nivo + 1) @
       (if trenutni_nivo = i then [x] else [])"



fun maksimalna_na_nivou_i :: "'a::ord drvo \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> nat"
  where
    "maksimalna_na_nivou_i List _ _ max = max"
  | "maksimalna_na_nivou_i (Cvor levo x desno) i trenutni_nivo max =
       (if trenutni_nivo = i then 
          max (max (maksimalna_na_nivou_i levo i (trenutni_nivo + 1) max) (maksimalna_na_nivou_i desno i (trenutni_nivo + 1) max)) x
       else 
          max (maksimalna_na_nivou_i levo i (trenutni_nivo + 1) max) (maksimalna_na_nivou_i desno i (trenutni_nivo + 1) max))"



(*
fun maksimalna_vrednost_na_nivou_i :: "int drvo \<Rightarrow> int \<Rightarrow> int \<Rightarrow> int option \<Rightarrow> unit" where
  "maksimalna_vrednost_na_nivou_i List _ _ _ = ()"
| "maksimalna_vrednost_na_nivou_i (Cvor levi x desni) i trenutni_nivo max =
     (maksimalna_vrednost_na_nivou_i levi i (trenutni_nivo + 1) max;
      maksimalna_vrednost_na_nivou_i desni i (trenutni_nivo + 1) max;
      (if trenutni_nivo = i then
         (case max of
            None \<Rightarrow> max := Some x
          | Some m \<Rightarrow> if x > m then max := Some x else ()) 
      else
        ()))"
*)

fun zbir_na_nivou_i :: "'a drvo \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a" where
  "zbir_na_nivou_i List _ _ = 0"
| "zbir_na_nivou_i (Cvor levo x desno) i trenutni_nivo =
     (if trenutni_nivo = i then 
        x 
      else 
        0) + 
     zbir_na_nivou_i levo i (trenutni_nivo + 1) + 
     zbir_na_nivou_i desno i (trenutni_nivo + 1)"




fun zbir_manjih_od_x :: "'a::ord drvo \<Rightarrow> 'a \<Rightarrow> 'a" where
  "zbir_manjih_od_x List _ = 0"
| "zbir_manjih_od_x (Cvor levo x desno) y =
     (if x <= y then 
        x + zbir_manjih_od_x levo y + zbir_manjih_od_x desno y 
      else 
        zbir_manjih_od_x levo y + zbir_manjih_od_x desno y)"

end