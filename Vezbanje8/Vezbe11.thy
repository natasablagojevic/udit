
(*<*)
theory Vezbe11
    imports Main
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle=stek mašina.]\<close>

text \<open>Definisati algebarski tip podataka \<open>izraz\<close> koji predstavlja
      izraz koga čine konstante koje su prirodni brojevi, i tri
      binarne operacije plus, minus, i puta nad izrazom.\<close>

datatype izraz  = 
  Const nat
  | Plus izraz izraz 
  | Minus izraz izraz 
  | Puta izraz izraz 

text \<open>Konstruisati proizvoljnu instancu tipa \<open>izraz\<close> i proveriti
      njenu ispravnost pomoću ključne reči \<open>term\<close>.\<close>

term "Plus (Const 2) (Const 4)"

text \<open>Definisati funkciju \<open>vrednost :: izraz \<Rightarrow> nat\<close> koja računa
      vrednost izraza.\<close>

fun vrednost:: "izraz \<Rightarrow> nat"
  where "vrednost (Const x) = x"
  | "vrednost (Plus x1 x2) = vrednost x1 + vrednost x2"
  | "vrednost (Minus x1 x2) = vrednost x1 - vrednost x2"
  | "vrednost (Puta x1 x2) = vrednost x1 * vrednost x2"

value "vrednost (Plus (Const 2) (Const 4))"

text \<open>Definisati izraze \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>, gde je
      $x_1 \equiv 2 + 3$, $x_2 \equiv 3 \cdot (5 - 2)$, i $x_3 \equiv 3 \cdot 4 \cdot (5 - 2)$.
      Izračunati vrednosti ovih izraza.\<close>

definition x1:: "izraz" where "x1 = Plus (Const 2) (Const 3)"
definition x2:: "izraz" where "x2 = Puta (Const 3) (Minus (Const 5) (Const 2))"
definition x3:: "izraz" where "x3 = Puta (Const 3) (Puta (Const 4) (Minus (Const 5) (Const 2)))"

text \<open>Definisati tip \<open>stek\<close> kao listu prirodnih brojeva. 
      Dodavanje na vrh steka podrazumeva operaciju 
      \<open>Cons\<close> (dodavanje na početak liste).\<close>

type_synonym stek = "nat list"


text \<open>Definisati algebarski tip \<open>operacija\<close> koji predstavlja
      moguće operacije koje će se izvršavati nad stekom.
      Nad stekom je moguće primeniti operaciju za plus,
      minus, puta i dodavanje nogov elementa na stek.\<close>

datatype operacija = 
  OpPlus 
  | OpMinus 
  | OpPuta
  | OpPush nat 

text \<open>Definisati funkciju \<open>izvrsiOp :: operacija \<Rightarrow> stek \<Rightarrow> stek\<close> koja 
      izvršava datu operaciju nad stekom i vraća novo stanje steka.\<close>

text \<open>Definisati tip \<open>program\<close> kao listu operacija.\<close>

text \<open>Definisati funkciju \<open>prevedi :: izraz \<Rightarrow> program\<close> koja
      data izraz prevodi u listu operacija, tj. program.
      Primeniti ovu funkciju nad izrazima \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>.\<close>

text \<open>Definisati funkciju \<open>izvrsiProgram :: program \<Rightarrow> stek \<Rightarrow> stek\<close>
      koja primenjuje listu operacija, tj. program nad stekom.
      Izračunati vrednost ove funkcije kada se primeni nad
      programom (koji se dobiju prevođenjem izraza \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>)
      i praznim stekom.\<close>

text \<open>Dodatno, definisati funkciju \<open>racunar :: izraz \<Rightarrow> nat\<close> koja
      prevodi program izvršava program (koji se dobija prevođenjem izraza)
      nad praznim stekom. Takođe, testirati ovu funkciju nad izrazima
      \<open>x1\<close>, \<open>x2\<close>, i \<open>x3\<close>.\<close>

text \<open>Pokazati da računar korektno izračunava vrednost izraza, tj. da su
      funkcije \<open>racunar\<close> i \<open>vrednost\<close> ekvivalentne.
      \<open>Savet\<close>: Potrebno je definisati pomoćne leme generalizacijom.\<close>

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
