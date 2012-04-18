\documentclass{scrartcl}
\usepackage[utf8]{inputenc}
\usepackage{hyperref}
\usepackage[ngerman]{babel}

\author{David Mihola (9902433)}
\title{Assignment 1: Ciphertext}

%include polycode.fmt
%options ghci
\begin{document}
\shorthandoff{"}
\maketitle
Ich habe ein Haskell-Programm geschrieben, um den Geheimtext zu entschlüsseln. Der vollständige Programmcode ist auch unter \url{https://github.com/DavidMihola/ItS-UE1} zu finden.

Zunächst importieren wir ein paar Funktionen, die wir später brauchen werden:

\begin{code}
import Data.List.Utils (hasAny)
import Char (toUpper, toLower)
import Data.Char (isLetter)
import Data.List ((\\), sort, sortBy)
import Data.Tuple (swap)
import Data.Function (on)
import Data.String.Utils (join)
\end{code}

Weiters kann es nicht schaden, den Geheimtext einmal als Zeichenkette abzuspeichern, um sie später zur Verfügung zu haben.

\begin{code}
cyphertext = "rlkmlj, zlnift ekblvke pqc elvm if pzlp gblrk, akrlomk \
\zk zle lfpiriglpke pzlp, if pzk flpojlb rcojmk cs knkfpm, morz qcobe \
\ak pzk rcfeorp cs nkjriftkpcjiu, bklnkm pzk ljdv ofekj gjkpkfmk cs \
\jlimift jkrjoipm lfe rlnlbjv: zk gblrkm ajopom, l vcoft dlf, if rcddlfe \
\cs pzkmk scjrkm; zk tinkm zid ifmpjorpicfm pzlp pzk rlnlbjv mzcobe jlftk \
\lm kupkfminkbv lm gcmmiabk if lbb eijkrpicfm; pzlp zk qcobe kukjp \
\zidmkbs fcp pc ak lamkfp sjcd pzk rldg bcftkj pzlf pzjkk elvm. zlnift \
\ljjlftke pzkmk dlppkjm, zk dljrzkm pc nikffl av lm bcft ycojfkvm lm zk \
\rlf, qzkf zim cqf mcbeikjm eie fcp kugkrp zid. sifeift pzkjk l sjkmz acev \
\cs rlnlbjv, qzirz zk zle mkfp cf pc pzlp gblrk mknkjlb elvm akscjk, \
\dljrzift ifrkmmlfpbv fitzp lfe elv, zk lenlfrke jlgiebv pzjcotz pzk \
\pkjjipcjv cs pzk lkeoi ifpc pzlp cs pzk biftcfkm, if qzirz pqc bkticfm \
\qkjk qifpkjift, pzlp, is lfv gblf lsskrpift zim cqf mlskpv mzcobe zlnk \
\akkf cjtlfiwke av pzk lkeoi, zk ditzp eksklp ip av pzk jlgieipv cs zim \
\dcnkdkfpm. qzkf zk ljjinke pzkjk, zk mkfem ifscjdlpicf pc pzk jkmp cs pzk \
\bkticfm, lfe tlpzkjm lbb zim ljdv ifpc cfk gblrk akscjk ifpkbbitkfrk cs \
\zim ljjinlb rcobe ak lffcofrke pc pzk ljnkjfi. nkjriftkpcjiu, cf zkljift \
\pzim rijrodmplfrk, bklem alrx zim ljdv ifpc pzk rcofpjv cs pzk aipojitkm; \
\lfe lspkj dljrzift sjcd ip pc tkjtcnil, l pcqf cs pzk acii, qzcd rlkmlj \
\zle mkppbke pzkjk lspkj eksklpift pzkd if pzk zkbnkpilf qlj, lfe zle \
\jkfekjke pjiaopljv pc pzk lkeoi, zk ekpkjdifke pc lpplrx ip."
\end{code}

Allgemeine Überlegungen: Die Angabe verrät schon, dass es sich bei der Verschlüsselungsmethode \emph{nicht} um Caesar's Cypher handelt, sondern um eine etwas kompliziertere Methode der Verschlüsselung.

Auf dieser Basis vermuten wir einmal, dass es sich bei der Verschlüsselung um eine einfache monoalphabetische Substition handelt. Ähnlich wie bei Caesar's Cypher würde dann jedes einzelne Zeichen des Klartextes bei der Verschlüsselung durch ein einzelnes Zeichen aus demselben Alphabet ersetzt und ähnlich wie bei Caesar's Cypher ist auch bei dieser Verschlüsselung die Zuordnung zwischen Zeichen des Klartextes und Zeichen des Geheimtextes für die ganze Botschaft konstant (d. h. die Ersetzung hängt nicht von der Position des Zeichens im Text ab). Im Gegensatz zu Caesar's Cypher handelt es sich allerdings nicht um eine einfache Verschiebung jedes Zeichens, sondern die Zuordnung ist beliebig.

Die Entschlüsselung eines auf diese Art codierten Geheimtextes ist relativ einfach, wenn man die relativen Häufigkeiten der Zeichen im Geheimtext analysiert und den relativen Häufigkeiten der Zeichen in der Sprache des Klartextes gegenüberstellt.

Aus der Angabe wissen wir, dass der Klartext in Englisch verfasst ist und Quellen wie Wikipedia (\url{http://en.wikipedia.org/wiki/Letter\_frequencies}) geben Aufschluss über die Häufigkeiten der verschiedenen Buchstaben in englischen Texten. (Wie sich herausstellen wird, reicht es für unsere Zwecke hier, zu wissen, dass das 'E' der häufigste Buchstabe in englischen Texten ist).

Es wäre sicherlich möglich, die Entschlüsselung eines solchen Geheimtextes vollständig zu automatisieren; für die Analyse eines einzelnen Textes ist es allerdings einfacher, sich ein paar einfache Funktionen zum Ersetzen einzelner Zeichen zu programmierung und sich dann von seiner Intuition leiten zu lassen.

Unser Ansatz dabei ist folgender: Wir wollen im Geheimtext nach und nach einzelne Zeichen durch das entsprechende Zeichen im Klartext ersetzen und uns so schrittweise vorarbeiten. Es ist hilfreich, dafür einen neuen Datentyp zu definieren, nämlich den Typ Letter. Es gibt zwei Arten von Letters, nämlich "original" (also Zeichen des Geheimtextes, die noch nicht ersetzt wurden) und "substituted" (also Zeichen, die schon durch das - hoffentlich richtige - Zeichen des Klartextes ersetzt wurden).

\begin{code}
data Letter = O Char | S Char deriving (Eq)
\end{code}

Um bei der Ausgabe leicht zwischen Originalzeichen und substituierten Zeichen unterscheiden zu können (und dennoch eine übersichtliche Ausgabe zu erhalten), stellen wir Originalzeichen als Kleinbuchstaben, substituierte Zeichen hingegen als Großbuchstaben dar.

\begin{code}
instance Show Letter where
  show (O c) = [toLower c]
  show (S c) = [toUpper c]
  showList ls s = (concatMap show ls) ++ s
\end{code}

Als ersten Schritt wandeln wir unseren Geheimtext (s. o.) in eine Liste von Letters um, und kennzeichnen jeden Buchstaben als Originalzeichen.

\begin{code}
original_cyphertext = map O cyphertext
\end{code}

Das Kernstück der Lösung sind die folgenden zwei Funktionen. Die Funktion substitute ersetzt jedes Auftreten eines Originalzeichens durch das entsprechende Substitutionszeichen. Es wird also sicher gestellt, dass ein bereits substituiertes Zeichen nicht weiter substituiert wird.

\begin{code}
substitute :: (Char, Char) -> [Letter] -> [Letter]
substitute pair = map (substitute' pair)

substitute' :: (Char, Char) -> Letter -> Letter
substitute' (old, new) l
    | l == (O old) = (S new)
    | otherwise = l
\end{code}

Für ein leichteres Arbeiten definieren wir noch eine Hilfsfunktion, die gleich eine ganze Liste von Subsitutionen nacheinander ausführt.

\begin{code}
subList :: [(Char, Char)] -> [Letter] -> [Letter]
subList subs list = foldr substitute list subs
\end{code}

Nachdem wir jetzt die Tools zum Ersetzen der Zeichen geschaffen haben, müssen wir noch herausfinden, welche Zeichen durch welche ersetzt werden sollen. Wie schon angedeutet ist es dafür wichtig, die Häufigkeiten der einzelnen Zeichen zu kennen. Dafür schreiben wir zunächste eine Funktion, die eine Liste durchgeht und für jedes Element speichert, wie oft es vorkommt. (Der Übersichtlichkeit halber wird die Liste auch gleich nach absteigender Häufigkeit sortiert.)

\begin{code}
frequencies :: Eq a => [a] -> [(a, Int)]
frequencies list = sortBy (flip compare `on` snd) unsorted
  where unsorted = foldl addOne [] list

        addOne :: Eq a => [(a, Int)] -> a -> [(a, Int)]
        addOne []     y = [(y, 1)]
        addOne ((x, n):xs) y
	      | (x == y)  = ((x, n+1):xs)
	      | otherwise = ((x, n):(addOne xs y))
\end{code}

Wir wollen uns nun ansehen, welche Buchstaben (Leerzeichen und Interpunktionszeichen interessieren uns hier nicht) mit welcher Häufigkeit vorkommen. :



\begin{code}
letter_frequencies = frequencies $ filter isLetter cyphertext
\end{code}

Der häufigste Buchstabe ist also das 'k', wahrscheinlich muss es also durch das 'e' zurückersetzt werden:

\begin{code}
step1 :: [Letter]
step1 = subList [('k', 'e')] original_cyphertext
\end{code}

rlEmlj, zlnift eEblvEe pqc elvm if pzlp gblrE, aErlomE zE zle lfpiriglpEe pzlp, if pzE flpojlb rcojmE cs EnEfpm, morz qcobe aE pzE rcfeorp cs nEjriftEpcjiu, bElnEm pzE ljdv ofeEj gjEpEfmE cs jlimift jErjoipm lfe rlnlbjv: zE gblrEm ajopom, l vcoft dlf, if rcddlfe cs pzEmE scjrEm; zE tinEm zid ifmpjorpicfm pzlp pzE rlnlbjv mzcobe jlftE lm EupEfminEbv lm gcmmiabE if lbb eijErpicfm; pzlp zE qcobe EuEjp zidmEbs fcp pc aE lamEfp sjcd pzE rldg bcftEj pzlf pzjEE elvm. zlnift ljjlftEe pzEmE dlppEjm, zE dljrzEm pc niEffl av lm bcft ycojfEvm lm zE rlf, qzEf zim cqf mcbeiEjm eie fcp EugErp zid. sifeift pzEjE l sjEmz acev cs rlnlbjv, qzirz zE zle mEfp cf pc pzlp gblrE mEnEjlb elvm aEscjE, dljrzift ifrEmmlfpbv fitzp lfe elv, zE lenlfrEe jlgiebv pzjcotz pzE pEjjipcjv cs pzE lEeoi ifpc pzlp cs pzE biftcfEm, if qzirz pqc bEticfm qEjE qifpEjift, pzlp, is lfv gblf lssErpift zim cqf mlsEpv mzcobe zlnE aEEf cjtlfiwEe av pzE lEeoi, zE ditzp eEsElp ip av pzE jlgieipv cs zim dcnEdEfpm. qzEf zE ljjinEe pzEjE, zE mEfem ifscjdlpicf pc pzE jEmp cs pzE bEticfm, lfe tlpzEjm lbb zim ljdv ifpc cfE gblrE aEscjE ifpEbbitEfrE cs zim ljjinlb rcobe aE lffcofrEe pc pzE ljnEjfi. nEjriftEpcjiu, cf zEljift pzim rijrodmplfrE, bElem alrx zim ljdv ifpc pzE rcofpjv cs pzE aipojitEm; lfe lspEj dljrzift sjcd ip pc tEjtcnil, l pcqf cs pzE acii, qzcd rlEmlj zle mEppbEe pzEjE lspEj eEsElpift pzEd if pzE zEbnEpilf qlj, lfe zle jEfeEjEe pjiaopljv pc pzE lEeoi, zE eEpEjdifEe pc lpplrx ip.


Relativ häufig kommt in dem Text nun ein Wort mit 3 Buchstaben vor, das auf e endet. Vielleicht handelt es sich dabei um "the"? Wir ersetzen probehalber 'z' durch 'h' und 'p' durch 't'.

\begin{code}
step2 = subList [('k','e'), ('z', 'h'), ('p','t')] original_cyphertext
\end{code}

rlEmlj, Hlnift eEblvEe Tqc elvm if THlT gblrE, aErlomE HE Hle lfTiriglTEe THlT, if THE flTojlb rcojmE cs EnEfTm, morH qcobe aE THE rcfeorT cs nEjriftETcjiu, bElnEm THE ljdv ofeEj gjETEfmE cs jlimift jErjoiTm lfe rlnlbjv: HE gblrEm ajoTom, l vcoft dlf, if rcddlfe cs THEmE scjrEm; HE tinEm Hid ifmTjorTicfm THlT THE rlnlbjv mHcobe jlftE lm EuTEfminEbv lm gcmmiabE if lbb eijErTicfm; THlT HE qcobe EuEjT HidmEbs fcT Tc aE lamEfT sjcd THE rldg bcftEj THlf THjEE elvm. Hlnift ljjlftEe THEmE dlTTEjm, HE dljrHEm Tc niEffl av lm bcft ycojfEvm lm HE rlf, qHEf Him cqf mcbeiEjm eie fcT EugErT Hid. sifeift THEjE l sjEmH acev cs rlnlbjv, qHirH HE Hle mEfT cf Tc THlT gblrE mEnEjlb elvm aEscjE, dljrHift ifrEmmlfTbv fitHT lfe elv, HE lenlfrEe jlgiebv THjcotH THE TEjjiTcjv cs THE lEeoi ifTc THlT cs THE biftcfEm, if qHirH Tqc bEticfm qEjE qifTEjift, THlT, is lfv gblf lssErTift Him cqf mlsETv mHcobe HlnE aEEf cjtlfiwEe av THE lEeoi, HE ditHT eEsElT iT av THE jlgieiTv cs Him dcnEdEfTm. qHEf HE ljjinEe THEjE, HE mEfem ifscjdlTicf Tc THE jEmT cs THE bEticfm, lfe tlTHEjm lbb Him ljdv ifTc cfE gblrE aEscjE ifTEbbitEfrE cs Him ljjinlb rcobe aE lffcofrEe Tc THE ljnEjfi. nEjriftETcjiu, cf HEljift THim rijrodmTlfrE, bElem alrx Him ljdv ifTc THE rcofTjv cs THE aiTojitEm; lfe lsTEj dljrHift sjcd iT Tc tEjtcnil, l Tcqf cs THE acii, qHcd rlEmlj Hle mETTbEe THEjE lsTEj eEsElTift THEd if THE HEbnETilf qlj, lfe Hle jEfeEjEe TjiaoTljv Tc THE lEeoi, HE eETEjdifEe Tc lTTlrx iT.

Noch zeigen sich keine offensichlichen Fehler, daher probieren wir weiter: 'l' wird duch 'a' ersetzt, damit bekommen wir ein "that" (das einzige Wort, das auf "th?t" passt).

\begin{code}
step3 = subList [('k','e'), ('z', 'h'), ('p','t'), ('l','a')] original_cyphertext
\end{code}

rAEmAj, HAnift eEbAvEe Tqc eAvm if THAT gbArE, aErAomE HE HAe AfTirigATEe THAT, if THE fATojAb rcojmE cs EnEfTm, morH qcobe aE THE rcfeorT cs nEjriftETcjiu, bEAnEm THE Ajdv ofeEj gjETEfmE cs jAimift jErjoiTm Afe rAnAbjv: HE gbArEm ajoTom, A vcoft dAf, if rcddAfe cs THEmE scjrEm; HE tinEm Hid ifmTjorTicfm THAT THE rAnAbjv mHcobe jAftE Am EuTEfminEbv Am gcmmiabE if Abb eijErTicfm; THAT HE qcobe EuEjT HidmEbs fcT Tc aE AamEfT sjcd THE rAdg bcftEj THAf THjEE eAvm. HAnift AjjAftEe THEmE dATTEjm, HE dAjrHEm Tc niEffA av Am bcft ycojfEvm Am HE rAf, qHEf Him cqf mcbeiEjm eie fcT EugErT Hid. sifeift THEjE A sjEmH acev cs rAnAbjv, qHirH HE HAe mEfT cf Tc THAT gbArE mEnEjAb eAvm aEscjE, dAjrHift ifrEmmAfTbv fitHT Afe eAv, HE AenAfrEe jAgiebv THjcotH THE TEjjiTcjv cs THE AEeoi ifTc THAT cs THE biftcfEm, if qHirH Tqc bEticfm qEjE qifTEjift, THAT, is Afv gbAf AssErTift Him cqf mAsETv mHcobe HAnE aEEf cjtAfiwEe av THE AEeoi, HE ditHT eEsEAT iT av THE jAgieiTv cs Him dcnEdEfTm. qHEf HE AjjinEe THEjE, HE mEfem ifscjdATicf Tc THE jEmT cs THE bEticfm, Afe tATHEjm Abb Him Ajdv ifTc cfE gbArE aEscjE ifTEbbitEfrE cs Him AjjinAb rcobe aE AffcofrEe Tc THE AjnEjfi. nEjriftETcjiu, cf HEAjift THim rijrodmTAfrE, bEAem aArx Him Ajdv ifTc THE rcofTjv cs THE aiTojitEm; Afe AsTEj dAjrHift sjcd iT Tc tEjtcniA, A Tcqf cs THE acii, qHcd rAEmAj HAe mETTbEe THEjE AsTEj eEsEATift THEd if THE HEbnETiAf qAj, Afe HAe jEfeEjEe TjiaoTAjv Tc THE AEeoi, HE eETEjdifEe Tc ATTArx iT.

Das Wort "atta??" in der letzten Zeile könnte "attack" heißen: Wir ersetzen also 'r' durch 'c', und 'x' durch 'k'.

\begin{code}
step4 = subList [('k','e'), ('z', 'h'), ('p','t'), ('l','a'),
                 ('r','c'), ('x','k')] original_cyphertext
\end{code}

CAEmAj, HAnift eEbAvEe Tqc eAvm if THAT gbACE, aECAomE HE HAe AfTiCigATEe THAT, if THE fATojAb CcojmE cs EnEfTm, moCH qcobe aE THE CcfeoCT cs nEjCiftETcjiu, bEAnEm THE Ajdv ofeEj gjETEfmE cs jAimift jECjoiTm Afe CAnAbjv: HE gbACEm ajoTom, A vcoft dAf, if CcddAfe cs THEmE scjCEm; HE tinEm Hid ifmTjoCTicfm THAT THE CAnAbjv mHcobe jAftE Am EuTEfminEbv Am gcmmiabE if Abb eijECTicfm; THAT HE qcobe EuEjT HidmEbs fcT Tc aE AamEfT sjcd THE CAdg bcftEj THAf THjEE eAvm. HAnift AjjAftEe THEmE dATTEjm, HE dAjCHEm Tc niEffA av Am bcft ycojfEvm Am HE CAf, qHEf Him cqf mcbeiEjm eie fcT EugECT Hid. sifeift THEjE A sjEmH acev cs CAnAbjv, qHiCH HE HAe mEfT cf Tc THAT gbACE mEnEjAb eAvm aEscjE, dAjCHift ifCEmmAfTbv fitHT Afe eAv, HE AenAfCEe jAgiebv THjcotH THE TEjjiTcjv cs THE AEeoi ifTc THAT cs THE biftcfEm, if qHiCH Tqc bEticfm qEjE qifTEjift, THAT, is Afv gbAf AssECTift Him cqf mAsETv mHcobe HAnE aEEf cjtAfiwEe av THE AEeoi, HE ditHT eEsEAT iT av THE jAgieiTv cs Him dcnEdEfTm. qHEf HE AjjinEe THEjE, HE mEfem ifscjdATicf Tc THE jEmT cs THE bEticfm, Afe tATHEjm Abb Him Ajdv ifTc cfE gbACE aEscjE ifTEbbitEfCE cs Him AjjinAb Ccobe aE AffcofCEe Tc THE AjnEjfi. nEjCiftETcjiu, cf HEAjift THim CijCodmTAfCE, bEAem aACK Him Ajdv ifTc THE CcofTjv cs THE aiTojitEm; Afe AsTEj dAjCHift sjcd iT Tc tEjtcniA, A Tcqf cs THE acii, qHcd CAEmAj HAe mETTbEe THEjE AsTEj eEsEATift THEd if THE HEbnETiAf qAj, Afe HAe jEfeEjEe TjiaoTAjv Tc THE AEeoi, HE eETEjdifEe Tc ATTACK iT.

Im Text kommt häufig das Wort "t?" vor, das wird wohl "to" heißen: 'c' wird durch 'o' ersetzt. Das erste des Textes Wort schaut verdächtig nach "caesar" aus: 'm' durch 's', 'j' durch 'r'.

\begin{code}
step5 = subList [('k','e'), ('z', 'h'), ('p','t'), ('l','a'),
                 ('r','c'), ('x','k'), ('c','o'),('m','s'),('j','r')] original_cyphertext
\end{code}

CAESAR, HAnift eEbAvEe TqO eAvS if THAT gbACE, aECAoSE HE HAe AfTiCigATEe THAT, if THE fAToRAb COoRSE Os EnEfTS, SoCH qOobe aE THE COfeoCT Os nERCiftETORiu, bEAnES THE ARdv ofeER gRETEfSE Os RAiSift RECRoiTS Afe CAnAbRv: HE gbACES aRoToS, A vOoft dAf, if COddAfe Os THESE sORCES; HE tinES Hid ifSTRoCTiOfS THAT THE CAnAbRv SHOobe RAftE AS EuTEfSinEbv AS gOSSiabE if Abb eiRECTiOfS; THAT HE qOobe EuERT HidSEbs fOT TO aE AaSEfT sROd THE CAdg bOftER THAf THREE eAvS. HAnift ARRAftEe THESE dATTERS, HE dARCHES TO niEffA av AS bOft yOoRfEvS AS HE CAf, qHEf HiS Oqf SObeiERS eie fOT EugECT Hid. sifeift THERE A sRESH aOev Os CAnAbRv, qHiCH HE HAe SEfT Of TO THAT gbACE SEnERAb eAvS aEsORE, dARCHift ifCESSAfTbv fitHT Afe eAv, HE AenAfCEe RAgiebv THROotH THE TERRiTORv Os THE AEeoi ifTO THAT Os THE biftOfES, if qHiCH TqO bEtiOfS qERE qifTERift, THAT, is Afv gbAf AssECTift HiS Oqf SAsETv SHOobe HAnE aEEf ORtAfiwEe av THE AEeoi, HE ditHT eEsEAT iT av THE RAgieiTv Os HiS dOnEdEfTS. qHEf HE ARRinEe THERE, HE SEfeS ifsORdATiOf TO THE REST Os THE bEtiOfS, Afe tATHERS Abb HiS ARdv ifTO OfE gbACE aEsORE ifTEbbitEfCE Os HiS ARRinAb COobe aE AffOofCEe TO THE ARnERfi. nERCiftETORiu, Of HEARift THiS CiRCodSTAfCE, bEAeS aACK HiS ARdv ifTO THE COofTRv Os THE aiToRitES; Afe AsTER dARCHift sROd iT TO tERtOniA, A TOqf Os THE aOii, qHOd CAESAR HAe SETTbEe THERE AsTER eEsEATift THEd if THE HEbnETiAf qAR, Afe HAe REfeEREe TRiaoTARv TO THE AEeoi, HE eETERdifEe TO ATTACK iT.

Wir raten weiter: 'i' bleibt 'i' (für das letzte Wort des Textes, "it"); 'f' durch 'n' zu ersetzen bietet sich an, da dadurch das häufige Wort 'in' entsteht; am Wortende kommt häufig das Bigramm "ng" vor, daher ersetzen wir das 't' durch 'g'; das 'e', das häufig am Wortende vorkommt, steht vermutlich für das 'd'; das 'q' kommt öfters an Stellen vor, wo man ein 'w' erwartet ("t?o"); und so weiter. Nach einigem weiteren Ausprobieren kommen wir so zum kompletten Code für die Rückübersetzung (wobei eben jeweils der erste Buchstabe eines Paares durch den zweiten Buchstaben ersetzt werden muss):

\begin{code}
code = [('k','e'), ('z','h'), ('p','t'), ('l','a'), ('r','c'),
        ('x','k'), ('c','o'), ('m','s'), ('j','r'), ('i','i'),
        ('f','n'), ('t','g'), ('e','d'), ('q','w'), ('v','y'),
        ('n','v'), ('b','l'), ('g','p'), ('o','u'), ('a','b'),
        ('s','f'),('d','m'),('u','x'),('w','z'),('y','j')]
\end{code}

Die Funktion zum Entschlüsseln des Textes lautet dann schließlich:

\begin{code}
decipher = subList code
\end{code}

Und der Klartext lautet:

\begin{code}
klartext = decipher original_cyphertext
\end{code}

CAESAR, HAVING DELAYED TWO DAYS IN THAT PLACE, BECAUSE HE HAD ANTICIPATED THAT, IN THE NATURAL COURSE OF EVENTS, SUCH WOULD BE THE CONDUCT OF VERCINGETORIX, LEAVES THE ARMY UNDER PRETENSE OF RAISING RECRUITS AND CAVALRY: HE PLACES BRUTUS, A YOUNG MAN, IN COMMAND OF THESE FORCES; HE GIVES HIM INSTRUCTIONS THAT THE CAVALRY SHOULD RANGE AS EXTENSIVELY AS POSSIBLE IN ALL DIRECTIONS; THAT HE WOULD EXERT HIMSELF NOT TO BE ABSENT FROM THE CAMP LONGER THAN THREE DAYS. HAVING ARRANGED THESE MATTERS, HE MARCHES TO VIENNA BY AS LONG JOURNEYS AS HE CAN, WHEN HIS OWN SOLDIERS DID NOT EXPECT HIM. FINDING THERE A FRESH BODY OF CAVALRY, WHICH HE HAD SENT ON TO THAT PLACE SEVERAL DAYS BEFORE, MARCHING INCESSANTLY NIGHT AND DAY, HE ADVANCED RAPIDLY THROUGH THE TERRITORY OF THE AEDUI INTO THAT OF THE LINGONES, IN WHICH TWO LEGIONS WERE WINTERING, THAT, IF ANY PLAN AFFECTING HIS OWN SAFETY SHOULD HAVE BEEN ORGANIZED BY THE AEDUI, HE MIGHT DEFEAT IT BY THE RAPIDITY OF HIS MOVEMENTS. WHEN HE ARRIVED THERE, HE SENDS INFORMATION TO THE REST OF THE LEGIONS, AND GATHERS ALL HIS ARMY INTO ONE PLACE BEFORE INTELLIGENCE OF HIS ARRIVAL COULD BE ANNOUNCED TO THE ARVERNI. VERCINGETORIX, ON HEARING THIS CIRCUMSTANCE, LEADS BACK HIS ARMY INTO THE COUNTRY OF THE BITURIGES; AND AFTER MARCHING FROM IT TO GERGOVIA, A TOWN OF THE BOII, WHOM CAESAR HAD SETTLED THERE AFTER DEFEATING THEM IN THE HELVETIAN WAR, AND HAD RENDERED TRIBUTARY TO THE AEDUI, HE DETERMINED TO ATTACK IT.

Wie schon eingangs erwähnt: Ich habe das Problem mit einer Mischung aus selbst geschriebenen Tools und eigenem Sprachgefühl gelöst. Ich habe zunächst auch einen anderen Ansatz probiert: Ich habe die Buchstaben nach absteigender Häufigkeit sortiert und dann jeden Buchstaben des Geheimtextes durch jenen Buchstaben ersetzt, der in englischen Texten den gleichen Rang in der Häufigkeit hat. Das hat aber nicht ganz funktioniert, da in dem vorliegenden Geheimtext die Häufigkeiten etwas anders verteilt sind: Während z. B. in englischen Texten allgemein das 's' etwas häufiger vorkommt als das 'r', ist es in unserem Geheimtext umgekehrt.

Ähnlich sieht es auch aus, wenn man Häufigkeitsverteilung der Wortanfangsbuchstaben betrachtet (diese unterscheidet sich von der Häufigkeitsverteilung der Buchstaben allgemein, d. h. manche Buchstaben kommen wesentlich öfter als Wortanfangsbuchstaben vor, als ihre allgemeine Häufigkeit vermuten ließe).

\begin{code}
first_letters :: [Char] -> [Char]
first_letters s = map head $ words s

first_letter_frequencies = frequencies $ first_letters cyphertext
\end{code}

Die häufigsten Anfangsbuchstaben sind laut Wikipedia "T A S H W L O B M F", in unserem Text allerdings "T A H O I B C D W S".

Auch interessant sind sicherlich die Häufigkeiten von Bigrammen und von Doppelbuchstaben:

\begin{code}
bigrams :: [Char] -> [[Char]]
bigrams text = concatMap bigrams' $ words text
  where bigrams' [] = []
        bigrams' (c:[]) = []
        bigrams' (c1:c2:cs) = (c1:[c2]):(bigrams' (c2:cs))

doubles :: [Char] -> [[Char]]
doubles text = filter same $ bigrams text
  where same (c1:c2:_) = c1 == c2

\end{code}

Die 20 häufigsten Buchstabenpaare sind laut Wikipedia "TH HE AN RE ER IN ON AT ND ST ES EN OF TE ED OR TI HI AS TO", in unserem Text hingegen "HE TH IN ER AN NG AR HA AT TO ES RE HI ED EN NT OF VE ON SE". Die häufigsten Doppelbuchstaben schließlich sind laut Wikipedia "LL EE SS OO TT FF RR NN PP CC", in unserem Text hingegen "RR LL TT SS EE NN MM FF II".

Eine reine Häufigkeitsanalyse von Buchstaben und Buchstabenpaaren alleine scheint also nicht auszureichen. Zusätzlich müsste man wohl ein Wörterbuch der Zielsprache verwenden, um gezielt Buchstaben dann zu ersetzen, wenn in einem Wort an einer gegebenen freien Stelle nur mehr ein einziger Buchstabe in Frage kommt (vgl. oben: "th?t" kann mit größter Wahrscheinlichkeit nur "that" heißen, daher muss der fragliche Buchstabe durch ein 'a' ersetzt werden).

\end{document}
