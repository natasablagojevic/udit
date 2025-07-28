
(*<*)
theory Vezbe09
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=Tip: list.]\<close>

text \<open>Diskutovati o sledećim termovima i vrednostima.\<close>

term "[]"
term "1 # 2 # []"
term "(1::nat) # 2 # []"
term "[1, 2]"
term "[1::nat, 2]"

value "[1..5]"
value "[1..<5]"

term sum_list
value "sum_list [1..<5]"

term map
term "\<lambda> x. f x"
value "map (\<lambda> x. x^2) [1..<5]"

value "sum_list (map (\<lambda> x. x^2) [1..<5])"
value "\<Sum> x \<leftarrow> [1..<5]. x^2"

term fold
term foldr
term foldl
value "fold (\<lambda> x acc. x^2 + acc) [1..<5] (0::nat)"
value "foldr (\<lambda> x acc. x^2 + acc) [1..<5] (0::nat)"
value "foldl (\<lambda> acc x. x^2 + acc) (0::nat) [1..<5]"

term filter
value "filter (\<lambda> x. x > 2) [1..<5]"

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Algebarski tip podataka: lista.]\<close>

text \<open>Definisati polimorfan algebarski tip podataka \<open>'a lista\<close>
      koji predstavlja listu elemenata polimorfong tipa \<open>'a\<close>.\<close>

datatype 'a lista = undef

term "Dodaj (1::nat) (Dodaj 2 (Dodaj 3 Prazna))"

text \<open>Definisati funkcije 
      \<open>duzina' :: 'a lista \<Rightarrow> nat\<close>, 
      \<open>nadovezi' :: 'a lista \<Rightarrow> 'a lista \<Rightarrow> 'a lista\<close>,
      \<open>obrni' :: 'a lista \<Rightarrow> 'a lista\<close>
      primitivnom rekurzijom koje računaju
      dužinu liste, nadoveziju i obrću liste tipa \<open>'a lista\<close>.\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Osnovne funkcije nad listama.]\<close>

text \<open>Definisati funkciju \<open>duzina :: 'a list \<Rightarrow> nat\<close> primitivnom rekurzijom 
      koja računa dužinu liste tipa \<open>'a list\<close>.
      Pokazati da su \<open>duzina\<close> i \<open>length\<close> ekvivalentne funkcije.\<close>

primrec duzina :: "'a list \<Rightarrow> nat" where
  "duzina [] = undefined"
| "duzina (x # xs) = undefined"

lemma duzina_length:
  shows "duzina xs = length xs"
  (*<*) oops (*>*)

text \<open>Definisati funkciju \<open>prebroj :: ('a::equal) \<Rightarrow> 'a list \<Rightarrow> nat\<close> primitivnom rekurzijom 
      koja računa koliko se puta javlja element tipa \<open>'a::equal\<close> u listi tipa \<open>('a::equal) list\<close>. 
      Pokazati da je \<open>prebroj a xs \<le> length xs\<close>.\<close>

text \<open>Definisati funkciju \<open>sadrzi :: ('a::equal) \<Rightarrow> 'a list \<Rightarrow> bool\<close> primitivnom rekurzijom
      koja ispituje da li se element tipa \<open>'a::equal\<close> javlja u listi tipa \<open>('a::equal) list\<close>.
      Pokazati da je \<open>sadrzi a xs = a \<in> set xs\<close>\<close>

text \<open>Definisati funkciju \<open>skup :: 'a list \<Rightarrow> 'a set\<close> primitivnom rekurzijom
      koja vraća skup tipa \<open>'a set\<close> koji je sačinjen od elemenata liste tipa \<open>'a list\<close>.
      Pokazati da je \<open>skup xs = set xs\<close>.\<close>

text \<open>Definisati funkciju \<open>nadovezi :: 'a list \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> primitivnom rekurzijom
      koja nadovezuje jednu listu na drugu tipa \<open>'a list\<close>.
      Pokazati da je ekvivalentna ugrađenoj funkciji \<open>append\<close> 
      ili infiksom operatoru \<open>@\<close>.\<close>

text \<open>Formulisati i pokazati da je dužina dve nedovezane liste, zbir dužina pojedinačnih listi.\\
      Orediti i dokazati osobine za funkcije \<open>skup\<close> i \<open>nadovezi\<close>, kao i za \<open>sadrzi\<close> i \<open>nadovezi\<close>.\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Obrtanje liste.]\<close>

text \<open>Definisati funkicju \<open>obrni :: 'a list \<Rightarrow> 'a list\<close> primitivnom rekurzijom
      koja obrće listu tipa \<open>'a list\<close>. 
      Pokazati da funkcija je \<open>obrni\<close> ekvivalentna funkciji \<open>rev\<close>.
      Nakon toga pokazati da je dvostruko obrnuta lista
      ekvivalentna početnoj listi.\\
      \<open>Napomena\<close>: Pri definisanju funkcije \<open>obrni\<close> nije dozvoljeno 
                  koristiti operator nadovezivanje \<open>@\<close>.\\
      \<open>Savet\<close>: Potrebno je definisati pomoćne leme.\<close>

primrec obrni :: "'a list \<Rightarrow> 'a list" where
  "obrni [] = undefined"
| "obrni (x # xs) = undefined"

lemma obrni_rev: 
  shows "obrni xs = rev xs"
  (*<*) oops (*>*)

lemma obrni_obrni_id: "obrni (obrni xs) = xs"
  (*<*) oops (*>*)

text \<open>Definisati funkciju \<open>snoc :: 'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> koja dodaje element 
      na kraj liste, i funkciju \<open>rev_snoc :: 'a list \<Rightarrow> 'a list\<close> koja uz pomoć 
      funkcije \<open>snoc\<close> obrće elemente liste. Da li \<open>rev_snoc\<close> popravlja složenost
      obrtanja liste?\<close>

primrec snoc :: "'a \<Rightarrow> 'a list \<Rightarrow> 'a list" where
  "snoc a [] = undefined"
| "snoc a (x # xs) = undefined"

primrec rev_snoc :: "'a list \<Rightarrow> 'a list" where
  "rev_snoc [] = undefined"
| "rev_snoc (x # xs) = undefined"

text \<open>Definisati funkciju \<open>itrev\<close> koja obrće listu iterativno.\\
      \<open>Savet\<close>: Koristiti pomoćnu listu.\<close>

text \<open>Pokazati da je funkcija \<open>itrev\<close> ekvivalentna ugrađenoj
      funkciji \<open>rev\<close>, kada je inicijalna pomoćna lista prazna.\<close>

text \<open>Pomoću funkcije \<open>fold\<close> opisati obrtanje liste.
      Pokazati ekvivalentnost funkciji \<open>itrev\<close> sa obrtanjem liste preko \<open>fold\<close>-a.\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle=Zamena u listi.]\<close>

text \<open>Definisati funkicju \<open>zameni :: 'a \<Rightarrow> 'a \<Rightarrow> 'a list \<Rightarrow> 'a list\<close> 
      primitivnom rekurzijom, tako da \<open>zameni a b xs\<close> u listi \<open>xs\<close> 
      zamenjuje sva pojavljivanja elementa \<open>a\<close> sa elementom \<open>b\<close>. 
      Pokazati da je funkcija \<open>zameni\<close> korektna preko zadatih lema.\\\<close>

lemma zameni_length: "length (zameni a b xs) = length xs"
  (*<*) oops (*>*)

lemma zameni_set: "a \<noteq> b \<Longrightarrow> a \<notin> set (zameni a b xs)"
  (*<*) oops (*>*)

lemma zameni_set2: "b \<in> set xs \<Longrightarrow> b \<in> set (zameni a b xs)"
  (*<*) oops (*>*)

text \<open>Definisati funkciju \<open>zameni'\<close> koja u listi zamenjuje određeni element drugim elementom.
      Funkcija \<open>zameni'\<close> treba da bude repno rekurzivna.\\
      \<open>Savet\<close>: Kao u primeru \<open>itrev\<close> koristiti pomoćnu listu.\<close>

lemma zameni'_len: "length (zameni' a b xs []) = length xs"
  (*<*) oops (*>*)

lemma zameni'_set: "a \<noteq> b \<Longrightarrow> a \<notin> set (zameni' a b xs [])"
  (*<*) oops (*>*)

lemma zameni'_set2: "b \<in> set xs \<Longrightarrow> b \<in> set (zameni' a b xs [])"
  (*<*) oops (*>*)

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
