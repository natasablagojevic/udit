
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
krila(x) = x ima krila 
lagano(x) = x je lagano 

\<forall>x. leti x \<longrightarrow> krila x 
\<forall>x. pliva x \<longrightarrow> \<not> krila x 
\<longrightarrow> \<forall>x. pliva x \<longrightarrow> \<not> leti x 

*)

lemma "(\<forall>x. leti x \<longrightarrow> krila x) \<and> (\<forall>x. pliva x \<longrightarrow> \<not> krila x) \<longrightarrow> (\<forall>x. pliva x \<longrightarrow> \<not> leti x)"
  by auto 

text \<open>(a.2) Ako postoji cipela koja u svakom trenutku odgovara svakoj nozi, 
            onda za svaku nogu postoji cipela koja joj u nekom trenutku odgovara 
            i za svaku nogu postoji trenutak takav da postoji cipela koja joj u tom 
            trenutku odgovara.\<close>

(*

A =  cipela koja u  trenutku odgovara nozi
B =  nogu  cipela koja joj u  trenutku odgovara
C =  nogu  trenutak takav da  cipela koja joj u trenutku odgovara

Odovara c t n 

A = \<exists>c. \<forall>t. \<forall>n. Odgovara c t n 
B = \<forall>n. \<exists>c. \<exists>t. Odgovara c t n 
C = \<forall>n. \<exists>t. \<exists>c. Odgovara c t n 

(\<exists>c. \<forall>t. \<forall>n. Odgovara c t n) \<longrightarrow> (\<forall>n. \<exists>c. \<exists>t. Odgovara c t n) \<and> (\<forall>n. \<exists>t. \<exists>c. Odgovara c t n)

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
Andrija 


P1: \<forall>x. srecan x \<longrightarrow> peva x 
P2: \<forall>x. peva x \<longrightarrow> plese x 
P3: srecan Andrija 
-------------------------
P:  plese Andrija 

*)

lemma "(\<forall>x. srecan x \<longrightarrow> peva x) \<and> (\<forall>x. peva x \<longrightarrow> plese x) \<and> (srecan Andrija) \<longrightarrow> plese Andrija"
  by auto 

text \<open>(b.2)\<close>
text \<open>P:  Svako dete voli da se igra.\<close>
text \<open>P1: Svaki dečak voli da se igra.\<close>
text \<open>P2: Svaka devojčica voli da se igra.\<close> 
text \<open>P3: Dete je dečak ili je devojčica.\<close>

(*

dete(x) = x je dete 
igra(x) = x voli da se igra 
decak(x) = x je decak 
devojcica(x) = x je devojcica 

P1: \<forall>x. decak x \<longrightarrow> igra x 
P2: \<forall>x. devojcica x \<longrightarrow> igra x 
P3: \<forall>x. dete x \<longrightarrow> decak x \<or> devojcica x 
-----------------------------------------
P:  \<forall>x. dete x \<longrightarrow> igra x 

*)

lemma "(\<forall>x. decak x \<longrightarrow> igra x) \<and> (\<forall>x. devojcica x \<longrightarrow> igra x) \<and> (\<forall>x. dete x \<longrightarrow> decak x \<or> devojcica x) \<longrightarrow> (\<forall>x. dete x \<longrightarrow> igra x)"
  by auto 

lemma 
  assumes "\<forall>x. decak x \<longrightarrow> igra x"
  assumes "\<forall>x. devojcica x \<longrightarrow> igra x"
  assumes "\<forall>x. dete x \<longrightarrow> decak x \<or> devojcica x"
  shows "\<forall>x. dete x \<longrightarrow> igra x"
proof
  fix x 
  show "dete x \<longrightarrow> igra x"
  proof
    assume "dete x"
    from this assms(3) have "decak x \<or> devojcica x" by auto 
    from this show "igra x"
    proof
      assume "decak x" 
      from this assms(1) show "igra x" by auto 
    next 
      assume "devojcica x"
      from this assms(2)  show "igra x" by auto 
    qed
  qed
qed


text \<open>(c) Na jeziku logike prvog reda zapisati sledeće rečenice i dokazati da su skupa nezadovoljive.\<close>

text \<open>- Svaka dva brata imaju zajedničkog roditelja.\<close>
text \<open>- Roditelj je stariji od deteta.\<close>
text \<open>- Postoje braća.\<close>
text \<open>- Nijedna osoba nije starija od druge.\<close>

(*

braca(x, y) = x je brat od y 
roditelj(x, y) = x je roditelj od y 
stariji(x, y) = x je stariji od y

\<forall>x. \<forall>y. \<exists>z. braca x y \<longrightarrow> roditelj z x \<and> roditelj z y
\<forall>x. \<forall>y. roditelj x y \<longrightarrow> satriji x y 
\<exists>x. \<exists> y. braca x y
 \<not>(\<exists>x. \<exists>y. stariji x y)
\<longrightarrow> False
*)

lemma "(\<forall>x. \<forall>y. \<exists>z. braca x y \<longrightarrow> roditelj z x \<and> roditelj z y) \<and> (\<forall>x. \<forall>y. roditelj x y \<longrightarrow> stariji x y) \<and> (\<exists>x. \<exists> y. braca x y) \<and> (\<not>(\<exists>x. \<exists>y. stariji x y)) \<longrightarrow> False"
  by auto 

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Silogizmi]\<close>

text \<open>Barbara (AAA-1)\<close>
text \<open>All men are mortal. (MaP)\<close>
text \<open>All Greeks are men. (SaM)\<close>
text \<open>— All Greeks are mortal. (SaP)\<close>

lemma Barbara: 
  assumes "\<forall>x. men x \<longrightarrow> mortal x"
  assumes "\<forall>x. greeks x \<longrightarrow> men x"
  shows "\<forall>x. greeks x \<longrightarrow> mortal x"
  using assms 
  by auto 

lemma Barbara2: 
  assumes "\<forall>x. men x \<longrightarrow> mortal x"
  assumes "\<forall>x. greeks x \<longrightarrow> men x"
  shows "\<forall>x. greeks x \<longrightarrow> mortal x"
proof
  fix x 
  show "greeks x \<longrightarrow> mortal x"
  proof
    assume "greeks x"
    from this assms(2) have "men x" by auto 
    from this assms(1) show "mortal x" by auto 
  qed
qed

text \<open>Celarent (EAE-1)\<close>
text \<open>Similar: Cesare (EAE-2)\<close>
text \<open>No reptiles have fur. (MeP)\<close>
text \<open>All snakes are reptiles. (SaM)\<close>
text \<open>— No snakes have fur. (SeP)\<close>

lemma  
  assumes "\<nexists>x. reptiles x \<and> fur x"
  assumes "\<forall>x. snakes x \<longrightarrow> reptiles x"
  shows "\<nexists>x. snakes x \<and> fur x"
    using assms
    by auto 
      
lemma  
  assumes "\<nexists>x. reptiles x \<and> fur x"
  assumes "\<forall>x. snakes x \<longrightarrow> reptiles x"
  shows "\<nexists>x. snakes x \<and> fur x"
proof
  assume "\<exists>x. snakes x \<and> fur x"
  from this obtain x where "snakes x \<and> fur x" by auto
  from this have "snakes x" "fur x" by auto 
  from this assms(2) have "reptiles x" by auto 
  from this \<open>fur x\<close> have "reptiles x \<and> fur x" by auto 
  from this have "\<exists>x. reptiles x \<and> fur x" by auto
  from this assms(1) show False by auto
qed


text \<open>Ferioque (EIO-1)\<close>
text \<open>No homework is fun. (MeP)\<close>
text \<open>Some reading is homework. (SiM)\<close>
text \<open>— Some reading is not fun. (SoP)\<close>

lemma 
  assumes "\<nexists>x. homework x \<and> fun x"
  assumes "\<exists>x. reading x \<and> homework x"
  shows "\<exists>x. reading x \<and> \<not> fun x"
  using assms 
  by auto

lemma 
  assumes "\<nexists>x. homework x \<and> fun x"
  assumes "\<exists>x. reading x \<and> homework x"
  shows "\<exists>x. reading x \<and> \<not> fun x"
proof -
  from assms(2) obtain x where "reading x \<and> homework x" by auto 
  then have "reading x" "homework x" by auto 
  show ?thesis 
  proof
    show "reading x \<and> \<not> fun x"
    proof
      from \<open>reading x\<close> show "reading x" by auto 
    next 
      show "\<not> fun x"
      proof
        assume "fun x"
        from this \<open>homework x\<close> have "homework x \<and> fun x" by auto 
        then have "\<exists>x. homework x \<and> fun x" by auto 
        from this assms(1) show False by auto 
      qed
    qed
  qed
qed


text \<open>Bocardo (OAO-3)\<close>
text \<open>Some cats are not pets. (MoP)\<close>
text \<open>All cats are mammals. (MaS)\<close>
text \<open>— Some mammals are not pets. (SoP)\<close>

lemma 
  assumes "\<exists>x. cats x \<and> \<not> pets x "
  assumes "\<forall>x. cats x \<longrightarrow> mammals x"
  shows "\<exists>x. mammals x \<and> \<not> pets x"
  using assms 
  by auto 

lemma 
  assumes "\<exists>x. cats x \<and> \<not> pets x "
  assumes "\<forall>x. cats x \<longrightarrow> mammals x"
  shows "\<exists>x. mammals x \<and> \<not> pets x"
proof -
  from assms(1) obtain x where "cats x \<and> \<not> pets x" by auto 
  then have "cats x" "\<not> pets x" by auto 
  show ?thesis
  proof
    show "mammals x \<and> \<not> pets x"
    proof
      from \<open>cats x\<close> assms(2) have "mammals x" by auto 
      from this show "mammals x" by auto 
    next 
      from \<open>\<not> pets x\<close> show "\<not> pets x" by auto
    qed
  qed
qed

text \<open>Barbari (AAI-1)\<close>
text \<open>All men are mortal. (MaP)\<close>
text \<open>All Greeks are men. (SaM)\<close>
text \<open>— Some Greeks are mortal. (SiP)\<close>

lemma 
  assumes "\<forall>x. men x \<longrightarrow> mortal x"
  assumes "\<forall>x. greeks x \<longrightarrow> men x"
  assumes "\<exists>x. greeks x"
  shows "\<exists>x. greeks x \<and> mortal x"
  using assms 
  by auto 

lemma 
  assumes "\<forall>x. men x \<longrightarrow> mortal x"
  assumes "\<forall>x. greeks x \<longrightarrow> men x"
  assumes "\<exists>x. greeks x"
  shows "\<exists>x. greeks x \<and> mortal x"
proof - 
  from assms(3) obtain x where "greeks x" by auto 
  show ?thesis 
  proof
    show "greeks x \<and> mortal x"
    proof
      from \<open>greeks x\<close> show "greeks x" by auto
    next 
      from \<open>greeks x\<close> assms(2) have "men x" by auto 
      from this assms(1) show "mortal x" by auto 
    qed
  qed
qed

text \<open>Celaront (EAO-1)\<close>
text \<open>No reptiles have fur. (MeP)\<close>
text \<open>All snakes are reptiles. (SaM)\<close>
text \<open>— Some snakes have no fur. (SoP)\<close>

lemma 
  assumes "\<nexists>x. reptiles x \<and> fur x" 
  assumes "\<forall>x. snakes x \<longrightarrow> reptiles x"
  assumes "\<exists>x. snakes x"
  shows "\<exists>x. snakes x \<and> \<not> fur x"
  using assms 
  by auto

lemma 
  assumes "\<nexists>x. reptiles x \<and> fur x" 
  assumes "\<forall>x. snakes x \<longrightarrow> reptiles x"
  assumes "\<exists>x. snakes x"
  shows "\<exists>x. snakes x \<and> \<not> fur x"
proof - 
  from assms(3) obtain x where "snakes x" by auto 
  show ?thesis
  proof
    show "snakes x \<and> \<not> fur x" 
    proof
      from \<open>snakes x\<close> show "snakes x" by auto 
    next 
      show "\<not> fur x"
      proof
        assume "fur x" 
        from \<open>snakes x\<close> assms(2) have "reptiles x" by auto 
        from this \<open>fur x\<close> have "reptiles x \<and> fur x" by auto 
        from this have "\<exists>x. reptiles x \<and> fur x" by auto 
        from this assms(1) show False by auto 
      qed
    qed
  qed
qed

text \<open>Camestros (AEO-2)\<close>
text \<open>All horses have hooves. (PaM)\<close>
text \<open>No humans have hooves. (SeM)\<close>
text \<open>— Some humans are not horses. (SoP)\<close>

lemma 
  assumes "\<forall>x. horses x \<longrightarrow> hooves x"
  assumes "\<nexists>x. human x \<and> hooves x"
  assumes "\<exists>x. human x"
  shows "\<exists>x. human x \<and> \<not> horses x"
  using assms 
  by auto 

lemma 
  assumes "\<forall>x. horses x \<longrightarrow> hooves x"
  assumes "\<nexists>x. human x \<and> hooves x"
  assumes "\<exists>x. human x"
  shows "\<exists>x. human x \<and> \<not> horses x"
proof - 
  from assms(3) obtain x where "human x" by auto 
  show ?thesis 
  proof
    show "human x \<and> \<not> horses x"
    proof
      from \<open>human x\<close>  show "human x" by auto 
    next 
      show "\<not> horses x"
      proof
        assume "horses x"
        from this assms(1) have "hooves x" by auto 
        from this \<open>human x\<close> have "human x \<and> hooves x" by auto 
        from this have "\<exists>x. human x \<and> hooves x" by auto 
        from this assms(2) show False by auto
      qed
    qed
  qed
qed

text \<open>Felapton (EAO-3)\<close>
text \<open>No flowers are animals. (MeP)\<close>
text \<open>All flowers are plants. (MaS)\<close>
text \<open>— Some plants are not animals. (SoP)\<close>

lemma 
  assumes "\<nexists>x. flowers x \<and> animals x"
  assumes "\<forall>x. flowers x \<longrightarrow> plants x"
  assumes "\<exists>x. flowers x"
  shows "\<exists>x. plants x \<and> \<not> animals x"
  using assms 
  by auto 

lemma 
  assumes "\<nexists>x. flowers x \<and> animals x"
  assumes "\<forall>x. flowers x \<longrightarrow> plants x"
  assumes "\<exists>x. flowers x"
  shows "\<exists>x. plants x \<and> \<not> animals x"
proof - 
  from assms(3) obtain x where "flowers x" by auto 
  show ?thesis
  proof
    show "plants x \<and> \<not> animals x"
    proof
      from \<open>flowers x\<close> assms(2) show "plants x" by auto 
    next 
      show "\<not> animals x" 
      proof
        assume "animals x"
        from this \<open>flowers x\<close> have "flowers x \<and> animals x" by auto 
        from this have "\<exists>x. flowers x \<and> animals x" by auto
        from this assms(1) show False by auto
      qed
    qed
  qed
qed

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Raymond M. Smullyan: Logical Labyrinths]\<close>

text \<open>Edgar Aberkrombi je bio antropolog koji se interesovao za logiku i socijologiju
      laganja i govorenja istine. Jednog dana je odlučio da poseti ostrvo vitezova i podanika.
      Stanovnike ovog ostrva delimo na one koji uvek govore istinu @{text "vitezove"} i
      one koji uvek govore laži @{text "podanike"}. Dodatno, na ostrvu žive samo vitezovi i 
      podanici. Aberkrombi susreće stanovnike i želi da prepozna ko je od njih vitez, 
      a ko je podatnik.\<close>

text \<open>1. Svaka osoba će odgovoriti potvrdno na pitanje: Da li si ti vitez?\<close>

lemma vitez: 
  assumes "k \<longleftrightarrow> (k \<longleftrightarrow> ans)"
  shows "ans"
  using assms
  by auto 

text \<open>1.1 Aberkombi je razgovarao sa tri stanovnika ostrva, označimo ih sa A, B i C. 
          Pitao je stanovnika A: ”Da li si ti vitez ili podanik?” 
          A je odgovorio ali nerazgovetno 
          pa je Aberkombi pitao stanovnika B: ”Šta je A rekao?” 
          B je odgovorio: ”Rekao je da je on podanik.” 
          Tada se uključila i osoba C i rekla: ”Ne veruj mu, on laže!” 
          Da li je osoba C vitez ili podanik?\<close>

lemma Smullyan_1_1:(*<*)
  assumes "kA \<longleftrightarrow> (kA \<longleftrightarrow> ansA)"
  assumes "kB \<longleftrightarrow> \<not> ansA"
  assumes "kC \<longleftrightarrow> \<not> kB"
  shows "kC"
proof - 
  from assms(1) have "ansA" using vitez[of kA ansA] by auto 
  with assms(2) have "\<not> kB" by auto 
  with assms(3) show "kC" by auto 
qed

text \<open>1.2 Aberkombi je pitao 
          stanovnika A koliko među njima trojicom ima podanika. 
          A je opet odgovorio nerazgovetno,
          tako da je Aberkombi pitao stanovnika B šta je A rekao. 
          B je rekao da je A rekao da su tačno dvojica podanici. 
          Ponovo je stanovnik C tvrdio da B laže. 
          Da li je u ovoj situaciji moguće odrediti da li je C vitez ili podanik?\<close>

definition exactly_two:: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool"
  where  "exactly_two A B C \<longleftrightarrow> ((A \<and> B) \<or> (A \<and> C) \<or> (B \<and> C)) \<and> \<not> (A \<and> B \<and> C)"

lemma Smullyan_1_2:
  assumes "kA \<longleftrightarrow> ansA"
  assumes "kB \<longleftrightarrow> (exactly_two (\<not>kA) (\<not>kB) (\<not>kC) \<longleftrightarrow> ansA)"
  assumes "kC \<longleftrightarrow> \<not>kB"
  shows "kC"
  using assms
  unfolding exactly_two_def
  by auto  


text \<open>1.3 Da li se zaključak prethodnog tvrđenja menja ako B promeni svoj odgovor 
          i kaže da je A rekao da su tačno dva od njih vitezovi?\<close>

lemma Smullyan_1_3:(*<*) 
  assumes "kA \<longleftrightarrow> ansA"
  assumes "kB \<longleftrightarrow> (exactly_two kA kB kC \<longleftrightarrow> ansA)"
  assumes "kC \<longleftrightarrow> \<not> kB"
  shows "\<not>kC"
  using assms
  unfolding exactly_two_def
  by auto 

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
