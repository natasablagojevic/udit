
(*<*)
theory Vezbe12
  imports Main "HOL-Library.Tree"
begin
(*>*)

text_raw \<open>\begin{exercise}[subtitle={Desni linearni lanac}]\<close>

text \<open>Data je funkcija \<open>rotiraj\<close> koja rotira drvo na sledeći način:\<close>

text_raw \<open>
\begin{center} 
\begin{forest} [b [a [t1] [t2]] [t3]] \end{forest} 
          -(rotiraj)$\rightarrow$ 
\begin{forest} [a [t1] [b [t2] [t3]]] \end{forest} 
\end{center}
\<close>

fun rotiraj :: "'a tree \<Rightarrow> 'a tree" where
  "rotiraj \<langle>\<langle>t1, a, t2\<rangle>, b, t3\<rangle> = \<langle>t1, a, \<langle>t2, b, t3\<rangle>\<rangle>"
| "rotiraj x = x"

thm rotiraj.simps

text_raw \<open>\begin{enumerate}\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Definisati funkciju \<open>bps :: ('a::linorder) tree \<Rightarrow> bool\<close> koja proverava 
      da li je stablo binarno pretraživačko. Za relaciju poretka koristiti \<open><\<close>,
      a za konstruisanje skupa elemenata stabla koristiti \<open>set_tree\<close>.\<close>

text \<open>Sledeća dva izraza moraju da se evaluiraju u \<open>True\<close>:\<close>

value "bps \<langle>\<langle>\<langle>\<langle>\<rangle>, 1::nat, \<langle>\<rangle>\<rangle>, 2, \<langle>\<rangle>\<rangle>, 5, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>"
value "\<not> bps \<langle>\<langle>\<langle>\<langle>\<rangle>, 3::nat, \<langle>\<rangle>\<rangle>, 2, \<langle>\<rangle>\<rangle>, 5, \<langle>\<langle>\<rangle>, 6, \<langle>\<rangle>\<rangle>\<rangle>"

text_raw \<open>\item (2p)\<close>

text \<open>Pokazati da je funkcija \<open>rotiraj\<close> korektna, tj. da funkcija \<open>rotiraj\<close> ne ruši svostvo
      binarnog pretraživačkog stabla i da skup čvorova ostaje nepromenjen nakon primene 
      funkcije \<open>rotiraj\<close>.\<close>

lemma "bps t \<Longrightarrow> bps (rotiraj t)"
  (*<*) oops (*>*)

lemma "set_tree (rotiraj t) = set_tree t"
  (*<*) oops (*>*)

text_raw \<open>\item (3p)\<close>

text \<open>Binarno stablo ima svojstvo \<open>desnog linearnog lanaca\<close> kada svaki unutrašnji čvor ima samo
      desnog potomka, tj. binarno stablo koje predstavlja listu duž desne strane. Definisati
      funkciju \<open>dll :: 'a tree \<Rightarrow> bool\<close> koja proverava da li je binarno stablo desni linearni
      lanac. \<open>Savet\<close>: Izbegavati \<open>if-then-else\<close> izraze, moguće je koristiti \<open>pattern matching\<close>.\<close>

text \<open>Sledeći izrazi moraju se evaluirati u \<open>True\<close> (pogledati i odgovarajuće slike).\<close>

value "dll \<langle>\<langle>\<rangle>, 1::nat, \<langle>\<langle>\<rangle>, 2, \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>" \<comment>\<open>(slika (a))\<close>
value "\<not> dll \<langle>\<langle>\<rangle>, 1::nat, \<langle>\<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>, 2, \<langle>\<rangle>\<rangle>\<rangle>" \<comment>\<open>(slika (b))\<close>
value "dll (rotiraj \<langle>\<langle>\<langle>\<rangle>, 1::nat, \<langle>\<rangle>\<rangle>, 2, \<langle>\<langle>\<rangle>, 3, \<langle>\<rangle>\<rangle>\<rangle>)" \<comment>\<open>(slika (c) --- pre rotiranja; slika (c') -- nakon rotiranja).\<close>

text_raw \<open>
\begin{center} 
(a) \begin{forest} [1 [.] [2 [.] [3 [.] [.]]]] \end{forest} 
(b) \begin{forest} [1 [.] [2 [3 [.] [.]] [.]]] \end{forest}
(c) \begin{forest} [2 [1 [.] [.]] [3 [.] [.]]] \end{forest}
(c') \begin{forest} [1 [.] [2 [.] [3 [.] [.]]]] \end{forest}
\end{center}
\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Definisati funkciju \<open>rotiraj1 :: 'a tree \<Rightarrow> 'a tree\<close> koja obilazi stablo i vrši prvu moguću
      rotaciju.\<close>

text \<open>Sledeći izraz mora da se evaluira u \<open>True\<close> (nakon 3 primene \<open>rotiraj1\<close> nema promena u stablu):\<close>

value "(rotiraj1 ^^ 3) \<langle>\<langle>\<langle>\<rangle>, 3::nat, \<langle>\<langle>\<rangle>, 5::nat, \<langle>\<langle>\<rangle>, 6::nat, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>, 1::nat, \<langle>\<langle>\<rangle>, 2::nat, \<langle>\<rangle>\<rangle>\<rangle>
      = (rotiraj1 ^^ 10) \<langle>\<langle>\<langle>\<rangle>, 3::nat, \<langle>\<langle>\<rangle>, 5::nat, \<langle>\<langle>\<rangle>, 6::nat, \<langle>\<rangle>\<rangle>\<rangle>\<rangle>, 1::nat, \<langle>\<langle>\<rangle>, 2::nat, \<langle>\<rangle>\<rangle>\<rangle>"

text_raw \<open>\item (2p)\<close>

text \<open>Želimo da dokažemo činjenicu da je najviše potrebno \<open>size t\<close> rotacija da bi binarno
      stablo postalo desni linearni lanac.\<close>

text \<open>Kako bi ovo pokazali moramo definisati meru zaustavljanja, tj. funkciju koja linearno 
      opada u odnosu na broj primena funkcije \<open>rotiraj1\<close> i dostiže \<open>0\<close> kada binarno stablo 
      postane desni linearni lanac. Jedna takva funkcija može biti definisana kao:\<close>

fun mera :: "'a tree \<Rightarrow> nat"  where
  "mera \<langle>\<rangle> = 0"
| "mera \<langle>l, a, r\<rangle> = size l + mera r"

text \<open>Pokazati da stablo \<open>t\<close> koje je desni linearni lanac uzima vrednost mere zaustavljanja 0.\<close>

lemma mera_0: "dll t \<longleftrightarrow> mera t = 0"
  (*<*) oops (*>*)

text_raw \<open>\item (2p)\<close>

text \<open>Pokazati da se mera smanjuje za 1 nakon primene funkcije \<open>rotiraj1\<close>.\<close>

lemma mera_rotiraj_1: "mera (rotiraj1 t) = mera t - 1"
  (*<*) oops (*>*)

text \<open>Pokazati da se mera smanjuje za \<open>n\<close> nakon \<open>n\<close> primena funkcija \<open>rotiraj1\<close>.\<close>

lemma mera_rotiraj_n: "mera ((rotiraj1 ^^ n) t) = mera t - n"
  (*<*) oops (*>*)

text_raw \<open>\item (2p)\<close>

text \<open>Konačno pokazati da:\<close>

theorem dll_rotiraj: "\<exists>n \<le> size t. dll ((rotiraj1 ^^ n) t)"
  (*<*) oops (*>*)

text_raw \<open>\end{enumerate}\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle={Fold-ovanje nad stablima}, points=10]\<close>

text_raw \<open>\begin{enumerate}\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Definisati tip \<open>'a ldrvo\<close> koji predstavlja binarno stablo koje čuva podatke samo u listovima.
      Definisati instancu \<open>test_drvo :: nat ldrvo\<close> tako da predstavlja sledeće drvo\<close>

text_raw \<open>\begin{center} \begin{forest} [. [. [2] [1]] [3]] \end{forest} \end{center}\<close>

text_raw \<open>\item (1p)\<close>

text \<open>Definisati funkciju \<open>lkd :: 'a ldrvo \<Rightarrow> 'a list\<close> koja vraća listu elemenata obilaskom 
      stabla metodom levo-koren-desno.\<close>

value "lkd test_drvo = [2,1,3]" \<comment>\<open>(Ovaj izraz mora da se evaluira u \<open>True\<close>)\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Jedan način foldovanja nad elementima ovog stabla je \<open>fold f (lkd d) acc\<close>. 
      Definisati funkciju \<open>fold_ldrvo :: ('a \<Rightarrow> 'b \<Rightarrow> 'b) \<Rightarrow> 'a ldrvo \<Rightarrow> 'b \<Rightarrow> 'b\<close>
      rekurzivno po strukturi drveta koja vraća isti rezultat kao i \<open>fold f (lkd d) acc\<close>.\<close>

text \<open>\<open>Napomena\<close>: Definisanje funkcije \<open>fold_ldrvo\<close> preko \<open>fold\<close> funkcije na iznad naveden način
      se ne priznaje kao tačno rešenje, već funckiju \<open>fold_ldrvo\<close> morate definisati 
      primitivnom rekurzijom.\<close>

value "fold_ldrvo (+) test_drvo 0 = 6" \<comment>\<open>(Ovaj izraz mora da se evaluira u \<open>True\<close>)\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Pokazati da je \<open>fold f (lkd d) acc = fold_ldrvo f d acc\<close>.\<close>

text_raw \<open>\item (1p)\<close>

text \<open>Definisati funkciju \<open>obrni :: 'a ldrvo \<Rightarrow> 'a ldrvo\<close> koja obrće stablo kao u ogledalu.\<close>

value "ldk (obrni test_drvo) = [3,1,2]" \<comment>\<open>(Ovaj izraz mora da se evaluira u \<open>True\<close>)\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Pokazati da je lkd poredak obrnutog drveta isto što i obrnuti lkd poredak početnog drveta.\<close>

text_raw \<open>\end{enumerate}\<close>

text_raw \<open>\end{exercise}\<close>

text_raw \<open>\begin{exercise}[subtitle={Odsecanje liste}]\<close>

text_raw \<open>\begin{enumerate}\<close>

text_raw \<open>\item (1p)\<close>

text \<open>Definisati funkciju \<open>sadrzi :: 'a \<Rightarrow> 'a list \<Rightarrow> bool\<close> koja ispituje da li se
      element nalazi u listi.\<close>

text \<open>Sledeća dva izraza se moraju evaluirati u \<open>True\<close>:\<close>

value "sadrzi 5 [1,6,2,5,3,4::nat] = True" \<comment>\<open>(Sadrži se)\<close>
value "sadrzi 8 [1,6,2,5,3,4::nat] = False" \<comment>\<open>(Ne sadrži se)\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Pokazati da je funkcija \<open>sadrzi\<close> invarijantna u odnosu na obrtanje liste.\<close>

text \<open>\<open>Savet\<close>: Definisati pomoćnu lemu koja opisuje da li se element nalazi u listi 
               kojoj znamo početak i poslednji element.\<close>

text_raw \<open>\item (1p)\<close>

text \<open>Definisati funkciju \<open>razliciti :: 'a list \<Rightarrow> bool\<close> koja ispituje
      da li su svi elementi liste međusobno različiti.\<close>

text \<open>Sledeća dva izraza se moraju evaluirati u \<open>True\<close>:\<close>

value "razliciti [1,6,2,5,3,4::nat] = True" \<comment>\<open>(Svi različiti)\<close>
value "razliciti [1,4,2,5,2,4::nat] = False" \<comment>\<open>(Ima istih)\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Pokazati da je funkcija \<open>razliciti\<close> invarijantna na obrtanje liste.\<close>

text_raw \<open>\item (3p)\<close>

text \<open>Pomoću funkcija \<open>fold\<close> i \<open>foldr\<close> definisati funkcije \<open>duzina_fold\<close> i \<open>duzina_foldr\<close>, 
      respektivno, koje računaju dužinu liste.\<close>

text \<open>Sledeći izrazi se moraju evaluirati u \<open>True\<close>.\<close>

value "duzina_fold [] = 0" \<comment>\<open>(Prazna lista)\<close>
value "duzina_fold [1,2,3::nat] = 3" \<comment>\<open>(Lista dužine 3)\<close>
value "duzina_foldr [] = 0" \<comment>\<open>(Prazna lista)\<close>
value "duzina_foldr [1,2,3::nat] = 3" \<comment>\<open>(Lista dužine 3)\<close>

text_raw \<open>\item (4p)\<close>

text \<open>Pokazati da su \<open>duzina_fold\<close> i \<open>duzina_foldr\<close> korektne, 
      tj. da daju isti rezultat kao i funkcija \<open>length\<close>.\<close>

text_raw \<open>\item (3p)\<close>

text \<open>Definisati funkciju \<open>iseci :: 'a list \<Rightarrow> nat \<Rightarrow> nat \<Rightarrow> 'a list\<close>. Za listu 
      $xs = [x_0,\ldots, x_n]$, poziv \<open>iseci xs s l\<close> vraća listu: 
      $[x_s,\ldots, x_{s+l-1}]$. Ako su vrednosti \<open>s\<close> i \<open>l\<close> van opsega
      funkcija \<open>iseci\<close> vraća kraću ili praznu listu.\<close>

text \<open>\<open>Savet\<close>: Koristite opštu rekurziju i \<open>pattern matching\<close>, umesto \<open>if-then-else\<close> izraza.
               Npr. umesto \<open>f s = (if s = 0 then e1 else e2)\<close> koristiti \<open>f 0 = e1\<close> i \<open>f s = e2\<close>.\<close>

text \<open>Sledeći izrazi se moraju evaluirati u \<open>True\<close>.\<close>

value "iseci [0,1,2,3,4,5,6::int] 2 3 = [2,3,4]" \<comment>\<open>(U opsegu)\<close>
value "iseci [0,1,2,3,4,5,6::int] 2 10 = [2,3,4,5,6]" \<comment>\<open>(Dužina van opsega)\<close>
value "iseci [0,1,2,3,4,5,6::int] 10 10 = []" \<comment>\<open>(Početni indeks van opsega)\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Pokazati da važi: \<open>iseci xs s l1 @ iseci xs (s + l1) l2 = iseci xs s (l1 + l2)\<close>\<close>

text_raw \<open>\item (2p)\<close>

text \<open>Pokazati da odsecanje liste zadržava invarijantnost o različitim elementima, tj.
      ako su elementi liste različiti, onda će biti različiti i elementi isečka.\<close>

text_raw \<open>\end{enumerate}\<close>

text_raw \<open>\end{exercise}\<close>

(*<*)
end
(*>*)
