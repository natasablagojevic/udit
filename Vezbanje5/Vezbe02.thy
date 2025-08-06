
(*<*)
theory Vezbe02
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Zapisivanje logičkih formula (nastavak)]\<close>

text \<open>(a) Zapisati sledeće rečenice u logici prvog reda i dokazati njihovu ispravnost.\<close>

text \<open>(a.1) Ako ”šta leti to ima krila i lagano je” 
            i ”šta pliva, to nema krila”, 
            onda ”šta pliva, to ne leti”\<close>

(*
leti(x) = x leti 
lagano(x) = x je lagano 
krila(x) = x ima krila 
pliva(x) = x pliva 

\<forall>x. leti x \<longrightarrow> krila x \<and> lagano x 
\<forall>x. pliva x \<longrightarrow> \<not> krila x 
\<forall>x. pliva x \<longrightarrow> \<not> leti x 
*)

lemma "(\<forall>x. leti x \<longrightarrow> krila x \<and> lagano x) \<and> (\<forall>x. pliva x \<longrightarrow> \<not> krila x) \<longrightarrow> (\<forall>x. pliva x \<longrightarrow> \<not> leti x)"
  by auto 

text \<open>(a.2) Ako postoji cipela koja u svakom trenutku odgovara svakoj nozi, 
            onda za svaku nogu postoji cipela koja joj u nekom trenutku odgovara 
            i za svaku nogu postoji trenutak takav da postoji cipela koja joj u tom 
            trenutku odgovara.\<close>

(*
c - cipela 
t - trenutak 
n - nozi 
odgovara c t n = cipela trenutku odgovara nozi 

\<exists>c. \<forall>t. \<forall>n. Odgovara c t n 
\<forall>n. \<exists>c. \<exists>t. Odgovara c t n 
\<forall>n. \<exists>t. \<exists>c. Odgovara c t n 

*)

lemma "(\<exists>c. \<forall>t. \<forall>n. Odgovara c t n) \<longrightarrow> (\<forall>n. \<exists>c. \<exists>t. Odgovara c t n) \<and> (\<forall>n. \<exists>t. \<exists>c. Odgovara c t n)"
  by auto 

text \<open>(b) Pokazati da je rečenica P logička posledica rečenica P1, P2, P3.\<close>

text \<open>(b.1)\<close>
text \<open>P:  Andrija voli da pleše.\<close>
text \<open>P1: Svako ko je srećan voli da peva.\<close>
text \<open>P2: Svako ko voli da peva, voli da pleše.\<close>
text \<open>P3: Andrija je srećan.\<close>

(*

plese(x) = x voli da plese 
srecan(x) = x je srecan 
peva(x) = x voli da peva 

p1: \<forall>x. srecan x \<longrightarrow> peva x 
p2: \<forall>x. peva x  \<longrightarrow> plese x 
p3: srecan Andrija
p: plese Andrija 

*)

lemma "(\<forall>x. srecan x \<longrightarrow> peva x) \<and> (\<forall>x. peva x \<longrightarrow> plese x) \<and> srecan Andrija \<longrightarrow> plese Andrija"
  by auto 

text \<open>(b.2)\<close>
text \<open>P:  Svako dete voli da se igra.\<close>
text \<open>P1: Svaki dečak voli da se igra.\<close>
text \<open>P2: Svaka devojčica voli da se igra.\<close> 
text \<open>P3: Dete je dečak ili je devojčica.\<close>

(*

dete(x) = x je dete 
igra(x) = x voli da se igra 
decak(x) = x je dacak 
devojcica(x) = x je devojcica 

p1: \<forall>x. decak x \<longrightarrow> igra x 
p2: \<forall>. devojcica x \<longrightarrow> igra x 
p3: \<forall>x. dete x \<longrightarrow> decak x \<or> devojcica x 
p: \<forall>x. dete x \<longrightarrow> igra x 

*)

lemma "(\<forall>x. decak x \<longrightarrow> igra x) \<and> (\<forall>x. devojcica x \<longrightarrow> igra x) \<and> (\<forall>x. dete x \<longrightarrow> decak x \<or> devojcica x) \<longrightarrow> (\<forall>x. dete x \<longrightarrow> igra x)"
  by auto 

text \<open>(c) Na jeziku logike prvog reda zapisati sledeće rečenice i dokazati da su skupa nezadovoljive.\<close>

text \<open>- Svaka dva brata imaju zajedničkog roditelja.\<close>
text \<open>- Roditelj je stariji od deteta.\<close>
text \<open>- Postoje braća.\<close>
text \<open>- Nijedna osoba nije starija od druge.\<close>

(*

brat(x, y) = x brat od y 
roditelj(x, y) = x je roditelj od y
starija(x, y) = x je stariji od y

\<forall>x. \<forall>y. \<exists>z.  brat x y \<longrightarrow> roditelj z x \<and> roditelj z y
\<forall>x. \<forall>y. roditelj x y \<longrightarrow> starija x y 
\<exists>x. \<exists>y. brat x y 
\<not>(\<exists>x. \<exists>y. starija x y)

*)

lemma "(\<forall>x. \<forall>y. \<exists>z.  brat x y \<longrightarrow> roditelj z x \<and> roditelj z y) \<and> (\<forall>x. \<forall>y. roditelj x y \<longrightarrow> starija x y) \<and> (\<exists>x. \<exists>y. brat x y ) \<and> (\<not>(\<exists>x. \<exists>y. starija x y)) \<longrightarrow> False"
  by auto 

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Silogizmi]\<close>

text \<open>Barbara (AAA-1)\<close>
text \<open>All men are mortal. (MaP)\<close>
text \<open>All Greeks are men. (SaM)\<close>
text \<open>— All Greeks are mortal. (SaP)\<close>

(*
men(x) = x je covek 
mortal(x) = x je smrtan 
greeks(x) = x je grk 

\<forall>x. men x \<longrightarrow> mortal x
\<forall>x. greeks x \<longrightarrow> men x 
\<forall>x. greeks x \<longrightarrow> mortal x 
*)

lemma Barbara: "(\<forall>x. men x \<longrightarrow> mortal x) \<and> (\<forall>x. greeks x \<longrightarrow> men x) \<longrightarrow> (\<forall>x. greeks x \<longrightarrow> mortal x)"
  by auto 

text \<open>Celarent (EAE-1)\<close>
text \<open>Similar: Cesare (EAE-2)\<close>
text \<open>No reptiles have fur. (MeP)\<close>
text \<open>All snakes are reptiles. (SaM)\<close>
text \<open>— No snakes have fur. (SeP)\<close>

(*

reptiles(x) = x je reptil 
fur(x) = x ima krzno 
snakes(x) = x je zmija 

\<nexists>x. reptiles x \<and> fur x 
\<forall>x. snakes x \<longrightarrow> reptiles x 
\<nexists>x. snakes x \<and> fur x 
*)

lemma Celarent: "(\<nexists>x. reptiles x \<and> fur x) \<and> (\<forall>x. snakes x \<longrightarrow> reptiles x) \<longrightarrow> (\<nexists>x. snakes x \<and> fur x)"
  by auto 

text \<open>Ferioque (EIO-1)\<close>
text \<open>No homework is fun. (MeP)\<close>
text \<open>Some reading is homework. (SiM)\<close>
text \<open>— Some reading is not fun. (SoP)\<close>

(*

homework(x) = x je domaci 
fun(x) = x je zabavan 
reading(x) = x je citanje 

\<nexists>x. homework x \<and> fun x 
\<exists>x. reading x \<and> homework x 
\<exists>x. reading x \<and> \<not> fun x 

*)

lemma Ferioque: "(\<nexists>x. homework x \<and> fun x) \<and> (\<exists>x. reading x \<and> homework x) \<longrightarrow> (\<exists>x. reading x \<and> \<not> fun x)"
  by auto 

lemma "(\<not>(\<exists>x. homework x \<and> fun x)) \<and> (\<exists>x. reading x \<and> homework x) \<longrightarrow> (\<exists>x. reading x \<and> \<not> fun x)"
  by auto 


text \<open>Bocardo (OAO-3)\<close>
text \<open>Some cats are not pets. (MoP)\<close>
text \<open>All cats are mammals. (MaS)\<close>
text \<open>— Some mammals are not pets. (SoP)\<close>

(*

cats(x) = x je macka 
pets(x) = x je kucni ljubimac 
mammals(x) = x je sisar 

\<exists>x. cats x \<and> \<not> pets x 
\<forall>x. cats x \<longrightarrow> mammals x 
\<exists>x. mammals x \<and> \<not> pets x

*)

lemma Bocardo:(*<*) "(\<exists>x. cats x \<and> \<not> pets x) \<and> (\<forall>x. cats x \<longrightarrow> mammals x) \<longrightarrow> (\<exists>x. mammals x \<and> \<not> pets x)"
  by auto 

text \<open>Barbari (AAI-1)\<close>
text \<open>All men are mortal. (MaP)\<close>
text \<open>All Greeks are men. (SaM)\<close>
text \<open>Exists Greeks\<close>
text \<open>— Some Greeks are mortal. (SiP)\<close>

(*

men(x) = x je covek 
mortal(x) = x je smrtan 
greeks(x) = x je grk 

\<forall>x. men x \<longrightarrow> mortal x
\<forall>x. greeks x \<longrightarrow> men x 
\<exists>x. greeks x \<and> mortal x 

*)

lemma Barbari: "(\<forall>x. men x \<longrightarrow> mortal x) \<and> (\<forall>x. greeks x \<longrightarrow> men x) \<and> (\<exists>x. greeks x) \<longrightarrow> (\<exists>x. greeks x \<and> mortal x)"
  by auto

text \<open>Celaront (EAO-1)\<close>
text \<open>No reptiles have fur. (MeP)\<close>
text \<open>All snakes are reptiles. (SaM)\<close>
text \<open>— Some snakes have no fur. (SoP)\<close>

lemma Celaront:(*<*) "(\<nexists>x. reptiles x \<and> fur x) \<and> (\<forall>x. snakes x \<longrightarrow> reptiles x) \<and> (\<exists>x. snakes x) \<longrightarrow> (\<exists>x. snakes x \<and> \<not> fur x)"
  by auto 

text \<open>Camestros (AEO-2)\<close>
text \<open>All horses have hooves. (PaM)\<close>
text \<open>No humans have hooves. (SeM)\<close>
text \<open>— Some humans are not horses. (SoP)\<close>

lemma Camestros: "(\<forall>x. horse x \<longrightarrow> hooves x) \<and> (\<nexists>x. human x \<and> hooves x) \<and> (\<exists>x. human x) \<longrightarrow> (\<exists>x. human x \<and> \<not> horse x)"
  by auto

text \<open>Felapton (EAO-3)\<close>
text \<open>No flowers are animals. (MeP)\<close>
text \<open>All flowers are plants. (MaS)\<close>
text \<open>— Some plants are not animals. (SoP)\<close>

lemma Felapton: "(\<nexists>x. flower x \<and> animal x) \<and> (\<forall>x. flower x \<longrightarrow> plant x) \<and> (\<exists>x. flower x) \<longrightarrow> (\<exists>x. plant x \<and> \<not> animal x)"
  by auto

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Raymond M. Smullyan: Logical Labyrinths]\<close>

text \<open>Edgar Aberkrombi je bio antropolog koji se interesovao za logiku i socijologiju
      laganja i govorenja istine. Jednog dana je odlučio da poseti ostrvo vitezova i podanika.
      Stanovnike ovog ostrva delimo na one koji uvek govore istinu @{text "vitezove"} i
      one koji uvek govore laži @{text "podanike"}. Dodatno, na ostrvu žive samo vitezovi i 
      podanici. Aberkrombi susreće stanovnike i želi da prepozna ko je od njih vitez, 
      a ko je podatnik.\<close>

text \<open>1. Svaka osoba će odgovoriti potvrdno na pitanje: Da li si ti vitez?\<close>

lemma no_one_admit_knaves: (*<*) "undefined"
  oops  (*>*)

text \<open>1.1 Aberkombi je razgovarao sa tri stanovnika ostrva, označimo ih sa A, B i C. 
          Pitao je stanovnika A: ”Da li si ti vitez ili podanik?” 
          A je odgovorio ali nerazgovetno 
          pa je Aberkombi pitao stanovnika B: ”Šta je A rekao?” 
          B je odgovorio: ”Rekao je da je on podanik.” 
          Tada se uključila i osoba C i rekla: ”Ne veruj mu, on laže!” 
          Da li je osoba C vitez ili podanik?\<close>

lemma Smullyan_1_1:(*<*) "undefined"
  oops  (*>*)
 

text \<open>1.2 Aberkombi je pitao 
          stanovnika A koliko među njima trojicom ima podanika. 
          A je opet odgovorio nerazgovetno,
          tako da je Aberkombi pitao stanovnika B šta je A rekao. 
          B je rekao da je A rekao da su tačno dvojica podanici. 
          Ponovo je stanovnik C tvrdio da B laže. 
          Da li je u ovoj situaciji moguće odrediti da li je C vitez ili podanik?\<close>

lemma Smullyan_1_2:(*<*) "undefined"
  oops (*>*)

text \<open>1.3 Da li se zaključak prethodnog tvrđenja menja ako B promeni svoj odgovor 
          i kaže da je A rekao da su tačno dva od njih vitezovi?\<close>

lemma Smullyan_1_3:(*<*) "undefined"
  oops  (*>*)

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
