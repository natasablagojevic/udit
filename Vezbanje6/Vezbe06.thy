
(*<*)
theory Vezbe06
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Isar dokazi u logici prvog reda.]\<close>

lemma 
  assumes "(\<exists> x. P x)"
      and "(\<forall> x. P x \<longrightarrow> Q x)"
    shows "(\<exists> x. Q x)"
proof -
  from assms(1) obtain x where "P x" by auto 
  from this assms(2) have "Q x" by auto 
  then show "\<exists>x. Q x" by auto
qed

lemma
  assumes "\<forall> c. Man c \<longrightarrow> Mortal c"
      and "\<forall> g. Greek g \<longrightarrow> Man g"
    shows "\<forall> a. Greek a \<longrightarrow> Mortal a"
proof
  fix x 
  show "Greek x \<longrightarrow> Mortal x"
  proof
    assume "Greek x"
    from this assms(2) have "Man x" by auto 
    from this assms(1) show "Mortal x" by auto
  qed
qed

text \<open>Dodatni primer:\<close>

text \<open>Ako svaki konj ima potkovice;\\
      i ako ne postoji čovek koji ima potkovice;\\
      i ako znamo da postoji makar jedan čovek;\\
      dokazati da postoji čovek koji nije konj.\<close>

(*

\<forall>x. konj x \<longrightarrow> potkovice x 
\<nexists>x. covek x \<and> potkovice x 
\<exists>x. covek x 
\<longrightarrow> \<exists>x. covek x \<and> \<not> konj x

*)

lemma 
  assumes "\<forall>x. konj x \<longrightarrow> potkovice x"
  assumes "\<nexists>x. covek x \<and> potkovice x"
  assumes "\<exists>x. covek x"
  shows "\<exists>x. covek x \<and> \<not> konj x"
proof -
  from assms(3) obtain x where "covek x" by auto 
  show ?thesis 
  proof
    show "covek x \<and> \<not> konj x"
    proof
      from \<open>covek x\<close> show "covek x" by auto
    next 
      show "\<not> konj x" 
      proof
        assume "konj x"
        from this assms(1) have "potkovice x" by auto 
        from this \<open>covek x\<close> have "covek x \<and> potkovice x" by auto 
        from this have "\<exists>x. covek x \<and> potkovice x" by auto 
        with assms(2) show False by auto 
      qed
    qed
  qed
qed

lemma 
  assumes "(\<forall>x. leti x \<longrightarrow> krila x)"
  assumes "(\<forall>x. pliva x \<longrightarrow> \<not> krila x)"
  shows "(\<forall>x. pliva x \<longrightarrow> \<not> leti x)"
proof
  fix x 
  show "pliva x \<longrightarrow> \<not> leti x"
  proof
    assume "pliva x"
    show "\<not> leti x"
    proof
      assume "leti x"
      from this assms(1) have "krila x" by auto 
      from \<open>pliva x\<close> assms(2) have "\<not> krila x" by auto
      from this \<open>krila x\<close> show False by auto 
    qed
  qed
qed

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
    then show "igra x" 
    proof 
      assume "decak x"
      from this assms(1) show "igra x" by auto 
    next 
      assume "devojcica x"
      from this assms(2) show "igra x" by auto 
    qed
  qed
qed

lemma  
  assumes "\<nexists>x. reptiles x \<and> fur x"
  assumes "\<forall>x. snakes x \<longrightarrow> reptiles x"
  shows "\<nexists>x. snakes x \<and> fur x"
proof
  assume "\<exists>x. snakes x \<and> fur x"
  from this obtain x where "snakes x \<and> fur x" by auto 
  from this have "snakes x" "fur x" by auto
  from \<open>snakes x\<close> assms(2) have "reptiles x" by auto 
  from this \<open>fur x\<close> have "reptiles x \<and> fur x" by auto 
  from this have "\<exists>x. reptiles x \<and> fur x" by auto
  with assms(1) show False by auto
qed

lemma 
  assumes "\<nexists>x. homework x \<and> fun x"
  assumes "\<exists>x. reading x \<and> homework x"
  shows "\<exists>x. reading x \<and> \<not> fun x"
proof -
  from assms(2) obtain x where "reading x \<and> homework x" by auto 
  then have "reading x" "homework x" by auto
  show "\<exists>x. reading x \<and> \<not> fun x" 
  proof 
    show "reading x \<and> \<not> fun x"
    proof
      from \<open>reading x\<close> show "reading x" by auto
    next
      show "\<not> fun x" 
      proof
        assume "fun x"
        from this \<open>homework x\<close> have "homework x \<and> fun x" by auto 
        from this have "\<exists>x. homework x \<and> fun x" by auto 
        with assms(1) show False by auto 
      qed
    qed
  qed
qed

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
      from assms(2) \<open>cats x\<close> show "mammals x" by auto
    next 
      from \<open>\<not> pets x\<close> show "\<not> pets x"  by auto     
    qed
  qed
qed

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
      from assms(2) \<open>greeks x\<close> have "men x" by auto
      with assms(1) show "mortal x" by auto 
    qed
  qed
qed

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
        with assms(1) show False by auto 
      qed
    qed
  qed
qed

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
        then have "\<exists>x. flowers x \<and> animals x" by auto
        with assms(1) show False by auto 
      qed
    qed
  qed
qed

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Pravilo ccontr i classical.]\<close>

text \<open>Dokazati u Isar jeziku naredna tvrđenja pomoću pravila \<open>ccontr\<close>.\<close>

lemma "\<not> (A \<and> B) \<longrightarrow> \<not> A \<or> \<not> B"
  sorry

text \<open>Dodatni primer:\<close>

lemma "((P \<longrightarrow> Q) \<longrightarrow> P) \<longrightarrow> P"
(*<*) oops (*>*)

text \<open>Dokazati u Isar jeziku naredna tvrđenja pomoću pravila \<open>classical\<close>.\<close>

lemma "P \<or> \<not> P"
(*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Logčki lavirinti.]\<close>

text \<open>Svaka osoba daje potvrdan odgovor na pitanje: \<open>Da li si ti vitez?\<close>\<close>

lemma no_one_admits_knave:
  assumes "k \<longleftrightarrow> (k \<longleftrightarrow> ans)"
    shows ans
(*<*) oops (*>*)

text \<open>Abercrombie je sreo tri stanovnika, koje ćemo zvati A, B i C. 
      Pitao je A: Jesi li ti vitez ili podanik?
      On je odgovorio, ali tako nejasno da Abercrombie nije mogao shvati 
      što je rekao. 
      Zatim je upitao B: Šta je rekao? 
      B odgovori: Rekao je da je podanik.
      U tom trenutku, C se ubacio i rekao: Ne verujte u to; to je laž! 
      Je li C bio vitez ili podanik?\<close>

lemma Smullyan_1_1:
  assumes "kA \<longleftrightarrow> (kA \<longleftrightarrow> ansA)"
      and "kB \<longleftrightarrow> \<not> ansA"
      and "kC \<longleftrightarrow> \<not> kB"
    shows kC
(*<*) oops (*>*)

text \<open>Abercrombie nije pitao A da li je on vitez ili podanik 
      (jer bi unapred znao koji će odgovor dobiti), 
      već je pitao A koliko od njih trojice su bili vitezovi. 
      Opet je A odgovorio nejasno, pa je Abercrombie upitao B što je A rekao. 
      B je tada rekao da je A rekao da su tačno njih dvojica podanici. 
      Tada je, kao i prije, C tvrdio da B laže. 
      Je li je sada moguće utvrditi da li je C vitez ili podanik?\<close>

definition exactly_two :: "bool \<Rightarrow> bool \<Rightarrow> bool \<Rightarrow> bool" where
  "exactly_two A B C \<longleftrightarrow> ((A \<and> B) \<or> (A \<and> C) \<or> (B \<and> C)) \<and> \<not> (A \<and> B \<and> C)"

lemma Smullyan_1_2:
  assumes "kB \<longleftrightarrow> (kA \<longleftrightarrow> exactly_two (\<not> kA) (\<not> kB) (\<not> kC))"
      and "kC \<longleftrightarrow> \<not> kB"
    shows "kC"
(*<*) oops (*>*)

text \<open>Abercrombie je sreo samo dva stanovnika A i B. 
      A je izjavio: Obojica smo podanici. 
      Da li možemo da zaključimo šta je A a šta je B?\<close>

text \<open>Dodatni primer:\<close>

lemma Smullyan_1_3:
  "x"
(*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
