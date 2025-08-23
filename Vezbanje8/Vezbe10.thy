
(*<*)
theory Vezbe10
    imports Main "HOL-Library.Multiset"
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Tip: 'a drvo]\<close>

text \<open>Definisati algebarski tip \<open>'a drvo\<close> koji predstavlja binarno drvo.\<close>

datatype 'a drvo = 
  List 
  | Cvor "'a drvo" 'a "'a drvo"

text \<open>Definisati funkciju \<open>zbir :: nat drvo \<Rightarrow> nat\<close> primitivnom rekurzijom koja 
      računa zbir elemenata drveta tipa \<open>nat drvo\<close>. Da li je moguće definisati ovu
      funkciju nad tipom \<open>'a drvo\<close>?\<close>

fun zbir:: "nat drvo \<Rightarrow> nat"
  where "zbir List = 0"
  | "zbir (Cvor levo x desno) = x + zbir levo + zbir desno"

text \<open>Definisati bilo koju instancu \<open>test_drvo\<close> tipa \<open>nat drvo\<close>. Proveriti
      da li funkcija \<open>zbir\<close> daje dobar rezultat kada se primeni na \<open>test_drvo\<close>.\<close>

definition tree_test:: "nat drvo" where  "tree_test \<equiv> Cvor (Cvor (Cvor List 1 List) 5 (Cvor (Cvor List 2 List) 3 (Cvor List 4 List))) 6 (Cvor (Cvor List 7 List) 8 (Cvor List 9 List))"
definition test_drvo:: "nat drvo" where  "test_drvo \<equiv> Cvor (Cvor List 1 List) 3 (Cvor (Cvor List 4 List) 2 (Cvor List 3 List))"

value "zbir test_drvo"

text \<open>Definisati funkciju \<open>sadrzi :: 'a drvo \<Rightarrow> 'a \<Rightarrow> bool\<close> primitivnom rekurzijom koja
      proverava da li se dati element nalazi u drvetu. Takođe, testirati funkciju nad 
      instancom \<open>test_drvo\<close>.\<close>

fun sadrzi:: "'a drvo \<Rightarrow> 'a \<Rightarrow> bool"
  where "sadrzi List a \<longleftrightarrow> False"
  | "sadrzi (Cvor levo x desno) a \<longleftrightarrow> (sadrzi levo a) \<or> (x = a) \<or> (sadrzi desno a)"


value "sadrzi test_drvo 11"

text \<open>Definisati funkciju \<open>skup :: 'a drvo \<Rightarrow> 'a set\<close> primitivnom rekurzijom koja
      proverava da li se dati element nalazi u drvetu. Takođe, testirati funkciju nad
      instancom \<open>test_drvo\<close>.\\
      Pronaći vezu između funkcija \<open>skup\<close> i \<open>sadrzi\<close>. Formulisati i dokazati tu lemu.\<close>

fun skup:: "'a drvo \<Rightarrow> 'a set"
  where "skup List = {}"
  | "skup (Cvor levo x desno) = skup levo \<union> {x} \<union> skup desno"

value "skup test_drvo"

lemma "x \<in> skup d \<longleftrightarrow> sadrzi d x"
  by (induction d) auto 

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Obilazak stabla]\<close>

text \<open>Definisati funkciju \<open>infiks\<close> koja vraća listu čvorova stabla u infiksnom poretku.\<close>

fun infiks:: "'a drvo \<Rightarrow> 'a list"
  where "infiks List = []"
  | "infiks (Cvor levo x desno) = infiks levo @ [x] @ infiks desno"

value "infiks tree_test"

fun prefiks:: "'a drvo \<Rightarrow> 'a list"
  where "prefiks List = []"
  | "prefiks (Cvor levo x desno) = [x] @ prefiks levo  @ prefiks desno"

value "prefiks tree_test"

fun postfiks:: "'a drvo \<Rightarrow> 'a list"
  where "postfiks List = []"
  | "postfiks (Cvor levo x desno) = postfiks levo @ postfiks desno @ [x]"

value "postfiks tree_test"


text \<open>Pokazati korektnost ove funkcije. Dve invarijante:\<close>
text_raw 
\<open>\begin{enumerate} 
  \item Skup elemenata infiksnog obilaska drveta i skup elemenata drveta ostaju isti.
  \item Multiskup elemanata infiksnog obilaska drveta i skupa elemenata drveta ostaju isti.
\end{enumerate}\<close>
text \<open>\<open>Savet\<close>: Tip multiskupa: \<open>'a multiset\<close>,
               prazan multiskup se definiše kao \<open>{#}\<close>, 
               multiskup sa jednim elementom \<open>{#x#}\<close>,
               unija multiskupova je operator \<open>+\<close>.\<close>

fun multiskup:: "'a drvo \<Rightarrow> 'a multiset"
  where "multiskup List = {#}"
  | "multiskup (Cvor levo x desno) = multiskup levo + {#x#} + multiskup desno"

value "multiskup test_drvo"
value "skup test_drvo"

lemma "set (infiks d) = skup d" 
  by (induction d) auto

lemma "mset (infiks d) = multiskup d"
  by (induction d) auto


text \<open>Definisati efikasnu implementaciju infiksnog obilaska drveta \<open>infiks_opt\<close> i 
      pokazati da je ekvivalentna funkciju \<open>infiks\<close>.\<close>

fun infiks_opt':: "'a drvo \<Rightarrow> 'a list \<Rightarrow> 'a list"
  where "infiks_opt' List acc = acc"
  | "infiks_opt' (Cvor levo x desno) acc = infiks_opt' levo (x # infiks_opt' desno acc)"

value "infiks_opt' tree_test []"

definition infiks_opt :: "nat drvo \<Rightarrow> nat list" where
  "infiks_opt xs = infiks_opt' xs []"

value "infiks_opt test_tree"

lemma infiks_opt_append:
  shows "infiks_opt' d xs @ ys = infiks_opt' d (xs @ ys)"
  by (induction d arbitrary: xs) auto 


lemma 
  shows "infiks d = infiks_opt d"
  unfolding infiks_opt_def 
  by (induction d) (auto simp add: infiks_opt_append)


text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Binarno pretraživačko stablo.]\<close>

text \<open>Definisati predikat \<open>sortirano\<close> nad binarnim stablom tipa \<open>('a::linorder) drvo\<close>
      koji ukazuje na to da li je stablo pretraživačko ili nije.
      Definisati instancu \<open>test_drvo_sortirano\<close> nad tipom \<open>nat drvo\<close> koja
      predstavlja binarno pretraživačko stablo. Testirati funkciju \<open>sortirano\<close>
      nad instancom \<open>test_drvo\<close> i \<open>test_drvo_sortirano\<close>.
      Zapisati i dokazati vezu između funkcije \<open>sortirano\<close> i \<open>infiks\<close>.\<close>

fun sortirano:: "('a::linorder) drvo \<Rightarrow> bool"
  where "sortirano List \<longleftrightarrow> True"
  | "sortirano (Cvor levo x desno) \<longleftrightarrow> sortirano levo \<and> sortirano desno \<and> (\<forall> a \<in> skup levo.  a \<le> x) \<and> (\<forall> a \<in> skup desno.  a > x)"

definition test_drvo_sortirano :: "nat drvo" where
  "test_drvo_sortirano = Cvor (Cvor List 1 (Cvor List 2 List)) 3 (Cvor (Cvor List 3 List) 4 List)"

definition tst_sort:: "nat drvo" where "tst_sort = Cvor (Cvor List 1 (Cvor List 2 List)) 3 (Cvor (Cvor List 4 List) 5 List)"

value "infiks test_drvo_sortirano"
value "sortirano test_drvo_sortirano"


value "infiks tree_test"
value "sortirano tree_test"

value "infiks tst_sort"
value "sortirano tst_sort"

text \<open>Primitivnom rekurzijom definisati funkciju \<open>ubaci :: 'a::linorder \<Rightarrow> 'a drvo \<Rightarrow> 'a drvo\<close>
      koja ubaciju element u binarno pretraživačko drvo.\<close>

fun ubaci:: "'a::linorder \<Rightarrow> 'a drvo \<Rightarrow> 'a drvo"
  where "ubaci a List = (Cvor List a List)"
  | "ubaci a (Cvor levo x desno) = (if a \<le> x then (Cvor (ubaci a levo) x desno) else (Cvor levo x (ubaci a desno)))"


text \<open>Pokazati da važe invarijante:\<close>
text_raw 
\<open>\begin{enumerate}
  \item Element će se nalaziti u drvetu nakon što se ubaci.
  \item Skup elemenata drveta nakon ubacivanja elementa se proširuje za taj element.
  \item Multiskup elemenata drveta nakon ubacivanja elementa se proširuje za taj element.
  \item Zbir elemenata drveta nakon ubacivanja elementa se povećava za njegovu vrednost.
  \item Nakon ubacivanja elementa u pretraživačko drvo, drvo ostaje pretraživačko.
\end{enumerate}\<close>

text \<open>Definisati funkciju \<open>listaUDrvo :: ('a::linorder) list \<Rightarrow> 'a drvo\<close> 
      koja od liste elemenata gradi binarno pretraživačko drvo.\<close>

fun listaUDrvo:: "('a::linorder) list \<Rightarrow> 'a drvo" 
  where "listaUDrvo []  = List"
  | "listaUDrvo (x#xs)  = ubaci x (listaUDrvo xs)"


text \<open>Pokazazati sledeće osobine funkcije \<open>listaUDrvo\<close>:\<close>
text_raw 
\<open>\begin{enumerate}
  \item listaUDrvo održava skup elemenata.
  \item listaUDrvo održava multiskup elemenata.
  \item listaUDrvo gradi binarno pretraživačko drvo.
\end{enumerate}\<close>

text \<open>Definisati funkciju koja sortira elemente liste pomoću stabla:\<close>

definition sortiraj :: "nat list \<Rightarrow> nat list" where
  "sortiraj xs = undefined"

text \<open>Pokazati korektnost ove funkcije\<close>
text_raw
\<open>\begin{enumerate}
  \item Nakon primene funkcije lista je sortirana.
  \item Skup elemenata sortirane liste i početne liste ostaje isit.
  \item Multiskup elemenata sortirane liste i početne liste ostaje isti.
\end{enumerate}\<close>

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
