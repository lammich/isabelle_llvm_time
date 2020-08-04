# Dienstag 4.8.

## Aktueller Stand

- Insertion Sort
  - beweise fertig
  - sepref synthese funktioniert
  - TODO:
      - kleinere sorries (extract hoare triple)
      - global_interpretation
- Heap Sort
  - Beweise fertig
  - TODO:
    - sepref synthese
      - wie vorgehen? manuel verfeinerung zu synthetisierbaren ops? oder automatisieren ?
- Refactoring
- Next steps

## Diskussion
- ll_call, mop_call,
- global_interpretation fixen
- diskussion parametrisieren vs higher-order
  - higher order bisher technisch nicht gut unterstützt
- diskussion, sepref verfeinerung von Heapsort
  - option A: in locale programm nochmal hinschreiben, per hand verfeinerung beweisen
  - option B: programm und verfeinerung + Zeitverfeinerung synthetisieren
  - option C: hnr aufbohren und Sepreftool konstante zeitverfeinerung synthetisieren lassen

![](time_synthesis.png)

- Verschiedene Arten von Verfeinerung
  - lockstep
  - SPEC verfeinerung
  - strukturell nicht gleich -> normalize blocks

![](types_of_refinement.png)
      
      
cmp a i j = a[i]<a[j]

sort (cmp a, xs, l , h)

closure_assn A xs a f fi =
(%fxs fia. A xs a ** pure(f, fi : A -> nat -> nat -> bool  & fxs=f xs & fia = fi a)) 

hnr ( ( closure_assn array_assn xs a cmp cmpi) cmpxs cmpia    )
 (doN { .... cmpxs }) ( ... ) bool_rel (doN { .... cmpia })



## Next Steps
### Max
- Heapsort fertig machen
  - mit Variante A: algorithmus nochmal hinschreiben, in sort_context_impl locale
  - refactor 
- introsort anschauen
- pdqsort

### Urlaub
- Max ab Fr 7.- Fr 14.
- Peter ab Fr 14.

## nächstes Treffen
wohl Donnerstag 6.8. 10 UKTime


  

      


# Treffen Mittwoch 22.7.2020

## IJCAR post-discussions
- Chargueraud 2016 Paper: https://hal.inria.fr/hal-01408670/document
- Fiat to Facade (chlipala)


## Max Kirchmeier
- Heute zu dritt treffen, oder morgen?
- was gibts zu besprechen?
- eher, compiler approach

## Aktueller Stand

- Insertion Sort: milestone, korrektheit und synthese per Sepref (still: einige Sorries)
- Heap Sort: 
    - sift_down_btu_correct
    - sift_down_restore_correct
    - sift_down1_refine_functional_aux
    - arbeite an sift_down1_refine_Time
      - einführung von leof, gwp_n und die zugehörigen Regeln. 
      
      
## TODO

### Max
- leof nach hinten schieben
- refinement beweise aufsetzten (paralellisierung ermöglichen)      -> "Trail of sorries"

### Peter
- "trail of sorries" reparieren




# Montag 22.6.

## TODOs
### Max
- gwp leof regeln
- refinement and vcg proofs bis functional goals
- issues erstellen

### Peter
- beweise retten

## Beobachtungen
- monadische operationen wie "lchild", "has_lchild" mit abstrakten währungen lassen
- TODO: Feingliederung in Sepref automatisieren, wenn die ausdrücke monadifiziert werden.
- ODER: händisch (weit im konkreten, ein schritt vor dem sepref Schritt) mit kosten_funktionen (first iteration)

## interessant
- Sorting_Heapsort.sift_down_param
  - parametrische compare funktion
  - "bis zum Schluss eine parametrische compare funktion vorhalten (auch durch Sepref)"
  - count "foreign function calls"
  - sort kostet "O (n * log n) cmp_funs"
  - daraus folgern,  falls cmp_fun kostet O(m) -> gesamt kostet O (n * log n * m)
  - CMP_ASSN cmp mycmp_impl 
  - "higher order separation logic" -> check for related work;

# Donnerstag 18.6.

## Erkenntnisse

- Währungen haben abhängigkeiten
- unser Ansatz erlaubt es nicht die Abhängigkeiten in den Währungen zu modellieren
- wie lösen? 3 schritte für das Interface
    1. alle währungen können noch versteckte abhängigkeiten haben (z.b. "slice_sort_spec")
    2. alle währungen ohne versteckte Abhaengigkeiten (z.b. "slice_insertionsort_spec")
    3. llvm implementierung, per hn_refine prädikat und nur konstanter umrechnungen.
  
- Inspektion von Heapsort und sift_down
- Trennung von Korrektheit und Laufzeit (per leof)

## TODOS

### Max
- leof theorie aufbauen
- Insertion Sort aufräumen
- algo <= SPEC X (\infinity) beweise streamlinen.
  - sollten die gleichen proof obligations rauskommen wie im alten framework
  - alle zusätzlichen proof obligation involving time gehen per simp weg (weil x <= \infinity <--> True)
  - Test with sift_down_btu_correct
  
  

# Montag 15.6.

insert_impl (hnr) insert3

insert3 l <= \Down(R l) ... sort_one_more_spec

insort1 = [ ... sort_one_more_spec ...]
** >= by refine_vcg **   B
insort2 = [ ... insert3 ...]
(hnr) by sepref       A
insort_impl

A[FCOMP B] geht nicht
-> zufuss selbst hinschreiben.

und dann:
    Hoaretriple extrahieren.
       
    
## TODO:

### Max:
- Sorting_Insertion_Sort fertig machen
    - code extract
    - hoare triple extract
    - clean up
    
## nächster schritt
- gemeinsam Heap Sort


# Fr 12.6.



## TODO

### Peter
- HNR für While
- 

### Max
- in Sorting_Insertion_Sort weiter
- solver für Summen mit simplifier



## Besprochen
- solver für "SUM (cost ni mi) <= SUM (cost nj mj)"
- solver für "SUM (cost ni mi) <= SUM (cost nj mj) - SUM (cost nk mk)"
- idee:
    -> runterbrechen auf constraints von enats
    -> könnte allein mit simplifier funktionieren.

lemma "a + c ≤ b ⟹ (a::nat) ≤ b - c" 
  by simp

- next steps:
    - kosten solver


# Mo 8.6.2020

## Fragestellung

Wie sieht das 'interface' fuer eine DS aus?
  - funktionale Korrektheit (klar)  
  - Timing ???

## TODO

### Max:
    - sepref_decl_op -> sepref_register und param lemma umschreiben (in Sorting_setup)
    - [params] regeln für nrest_rules
    -

### Peter:
    - FCOMP bug with raw assns.

## Notizen

Interface:
    (mop_list_nth c) xs i == 


NEXT STEPS:
    - sepref_decl_op / sepref_decl_inft weglassen
    - statt dessen sepref_register verwenden (mit context T)
    - param_mop regel beweisen
    - FCOMP verwenden um hnr theoreme zusammenzubauen (element verfeinerung mit hnr_raw lemma + param lemma), fcomp_norm_simps verwenden um hr_comp zusammenzufassen
    - 


FCOMP
FCOMP (unchecked)


 param(114): ((⤜), (⤜)) ∈ ⟨?Ra⟩nres_rel → (?Ra → ⟨?Rb⟩nres_rel) → ⟨?Rb⟩nres_rel
 
Results
  param(113): ⟦(?Φ, ?Ψ) ∈ bool_rel; ⟦?Φ; ?Ψ⟧ ⟹ (?f, ?g) ∈ ⟨?R⟩nres_rel⟧ ⟹ (do {
                                                                                  _ ← ASSERT ?Φ;
                                                                                  ?f
                                                                                }, do {
                                                                                  _ ← ASSERT ?Ψ;
                                                                                  ?g
                                                                                })
                                                                               ∈ ⟨?R⟩nres_rel


*********************************
(uncurry extract_impl, uncurry mop_eo_extract) ∈ eo_assn⇧d *⇩a snat_assn⇧k →⇩a⇩d (λx (ai, uu_). elem_assn ×⇩a cnc_assn (λx. x = ai) eo_assn)



hn_refine (hn_ctxt (eoarray_assn ?A) ?a ?ai ∧* hn_val snat_rel ?b ?bi) (eo_extract_impl $ ?ai $ ?bi) (hn_invalid (eoarray_assn ?A) ?a ?ai ∧* hn_val snat_rel ?b ?bi)
 (?A ×⇩a eoarray_assn ?A) (mop_eo_extract $ ?a $ ?b)


weitergehts um 12:45 (UKtime)

- "flexibilität die man im abstrakten nicht hat, kann man im konkreten nicht erwarten"

- erst konzentration ohne BFS4/9 idee:

xs <- list_append (List4op) xs a

1. Schritt
C = do { ... list_append (cost_array_list_append) xs a 
... }
<= E  do { ... list_append (1 $List4op) xs a ... } = E A


A= do { ..... mop (1 $c) xs a ,..... }

C= do { ..... mop c' xs a ,..... }

list_append (E c) xs a <=E list_append c xs a
 c' = ?E c 
 
 c'' = ?E c
 
 
 ?c <= E a
 
 
 list_append cost_array_list = cosume ... (SPEC ())

sepref_decl_op list_append

list_append_param: list_append,list_append : A rel_list -> A -> A rel_list rel_nrest

sepref_decl_impl: hnr_thm
  -> list_append_param[FCOMP hnr_thm]
  
  hnr_thm: hnr (raw_array_assn xs xsi) ...
  
 hnr (hf_comp (raw_array_assn) (A list_rel)) ...  
 definition [symmetric, fcomp_norm_simp]: "array_assn A == hf_comp (raw_array_assn) (A list_rel)"
  
***************************************
  
  a *<param>* b <hnr> c
  
  a <hnr> c
  


 
 sepref_decl_op
 - definiert op
 - definiert mop
 - definiert tmop
 
 sepref_decl_impl
 - wrapper für FCOMP
 - 
 
mop_list_append = ...
tmop_list_append T  := consume T mop_list_append
 
 
mop_set_insert ($HASH_comp + $ARRAY_UPDATE) 
....
mop_set_insert (int_hash_comp + array_list_update) 
 
 
 
list_append (sup array_list linked_list) xs x

sup E1 E2 = (%x. sup (E1 x) (E2 x))

fun E =
where "E $A $B = 1"
"E $A _ = 0"
" ...."
konkreter vorgang:
    - C explizit angeben (in do notation)
    - C <= ?E A   beweisen (refine_rcg) 

2 möglichkeiten:
    - C angeben und E synthetisieren (uniform mitrefinement approach jetzt, ist aber nur ne Notlösung)
    - E angeben und C synthetisieren (
list_append (E c) xs a <=E list_append c xs a

dann: Sepref

simplify E list4op -> cost_array_list_append


xs <- list_append (cost_array_list_append) xs a

cost_array_list_append: basic layer costs
definition cost_array_list_append = cost ''ll_call'' 1 + ...

2. Schritt

hnr (array_list) ... (list_append (cost_array_list_append) xs a)


->



---------



basic layer: ll_call, ll_read, ll_write

hnr 
(array_list xs xsi) *?c* ?Gamma ?R
?a (list_append (list4) xs a)




consume O(1) list_append
tmop = consume (???) mop_...

mimpl <= R,E SPEC(sort,__ n*47*$CMP __)  
                         i                           iiiiiiiiiiiiiiiiii

t' n = n*47*$CMP

t = E(t')

t'' = E1 E2 E3 * SPEC

t'' 

t :: param => ([currency*** =>] enat)
 t A1 = (cost call 15 + cost read 16) 

hnr .....       (E SPEC (sort, t')

E -> t' ---> t

< $ t A1 * assn C1 A2...> c C1 C2 <...> 

Time Algorithmus c a <= %a. Sum(t a) 

/\  Sum (t a) UNIV : THETA ( F )

-------------------------
(\exists t:Theta F. <$t ...> c <> )
<==>
(\exists t:O( F ). <$t ...> c <> )
<==>
"c ist functional correct und läuft in WCET O(F)"


Sum t <= O(NlogN)
f_proj S1 t <= O(NlogN)
f_proj S2 t <= O(N)
S1 union S2 = UNIV



Sum(t)  : O(n...) 
<--->
\forall x. t x <= O(...)


Sum t = { t x | x:UNIV }



proj_ll_lookup t   : O(n....)
proj_ll_le t   : O(n....)

O(nlogn($CMP+$MOV+1))

element: int
$CMP->1 $ LL_call
$CMP->1 $ LL_read
$MOV->O(1)

-> O(nlogn)


SUM_projection f = sum 

SUM_projection (%xs. intro_sort xs) : O( n log n)



needed: mechanism that makes sure that no operations/costs are dropped
- projection alone does not make sure that things are dropped


mop_list_append t x xs = SPECT [ xs @ [x] |-> t ]
= consume [ ... ] t

lists_app_O1 = list_append (1 $constant_list_append) x xs
O(1) 

DS1: append     OP1
DS2 : append    OP2

E * OP1 + V * Op2

E * (OP1+OP2) + V* (Op1+Op2)

Op2: V,      E+V


do {
    ...

ys <. list_append (1 $constant_list_append) x xs
O(1) 


}

https://en.cppreference.com/w/cpp/container/vector






Effekt:
    - abstrakte datenstrukturen mit unterschiedlichen konkreten datenstrukturen verfeinern,
      - dazu unterschiedliche Currencies einführen?

Umrechnung bei Seprefschritt:
    - JA:
- 
    - NEIN:
        
        
- interfaces weiter aufteilen
  - bisher: zwischen interfaces aufteilen (listen, sets, maps)
  - weiteraufteilen in (log-lookup-sets, amortized-linear-sets,.. .)
  - operations spezifisch zusätzlich die gewüschte timing charakteristik (listen operation mit O(1))
  - dann adhoc:        
      
      
        
Ablauf Sepref:
    - abstraktes NREST programm
    - manuelle rewrites an den stellen der Konstruktoren der Datenstrukturen (rewrite X )
    - id_phase (operationen flachklopfen, z.b. map_update)
    - monadification
    - jetzt nach sepref (HNR)
    - Synthese


# Fr 29.5.2020

## TODOS:
    
### Peter
- solve seprefregister issue
- prove_prems into Utils

### max
- issue erstellen für "sepref_register"
- FCOMP sup_attains
  - solver für "BLA"-goals
- weitermachen mit Sepref_HOL_Bindings
- hn_refine_frame rule beweisen

## Probleme die uns noch bevor stehen:
- Kosten von Produkte
  - Lösung: erstmal im konkreten auf null setzen?
    - insert_element, extract_element := 0
  - Lösung: im abstrakten auf infinity setzen 


## Notes

    (* Prove premises of theorem by given tactics. Warning: Simultaneous semantics, 
      will fail/misbehave if tactic instantiates schematic that occurs in later premise to be proved *)
    val prove_prems: Proof.context -> thm -> (Proof.context -> int -> tactic) option list -> thm


  |> prove_prems ctxt [NONE,NONE,SOME your_tac]

  thm[OF _ _ tac1 tac2 _ ]
  
  
  (a,b,c) <- while ... (a,b,c)
  
  pair1 = mop_pair b c
  pair2 = mop_pair a pair1
  
  res <- while ... pair2


# Donnerstag 28.5. 


ref1: a1 <= SPEC P (%_. t)
ref2: a2 <= R1 a1 
ref3: a3 <= R2 a2 
ref_impl: hn_refine a_impl a3 R3


->

ref_impl FCOMP (ref3 FCOMP ref2 FCOMP ref1)

(ref_impl FCOMP ref3) FCOMP ref2 FCOMP ref1


## mögliches vorgehen

vorgehen "zusammenschieben":
- refX beweisen
- ref_impl synthestisieren von ref3
- ref1-ref3 zusammenschieben -> ref3 <= R SPEC
- composition mit SideCondition "sup_attains ref_impl SPEC R"
-> neues hnr lemma


## How to solve sup_attains Side conditions

SV R ==> sup_attains R m
sup_attains R (ASSERT; CONSUME (RETURN x) c)


onetime ((ASSERT; CONSUME (RETURN x) c)) 
onetime M ==> sup_attains R M

m'  <= DOWN R2 m''

LEMMA:
impl  (hnr A)  m <= \Down R  m'
sup_attains R m'
------------
impl (hnr (hr_comp A R)) m'

## test für intuition
side conditions bei 2 regel anwendungen vs sidecondition bei zusammen schieben und dann 1 regelanwendung:

\exists m'. (
SC1: sup_attains R m'
m'  <= DOWN R2 m''
SC2: sup_attains R2 m'' )
--------------------------------
sup_attains (R O R2) m''

problem (glaub ich) :
    sup_attains R1; sup_attains R2
    =/=> sup_attains (R1 O R2)

TODO: beispiel finden

conjecture:
sup_attains m (\down R2 m') R1
==> sup_attains m m' (R1 O R2)
    
    
    
    lemma 
        "sup_attains m (SPECT (emb' P (%_. t))) RR"
        
        
Angenommen:
- alle DS haben konstante Zeit  

## kriterien für sup_attains

m <= \Down R m'
single_valued R

single_costed R m' =
single_valued ({(x,c) | (x,y) : R & m' y = Some c  }    )

one_time m = single_costed UNIV m

single_costed RR m'  ==> sup_attains m m' RR


## Side Problem
        
R1: (n,c,xs) |-> take n xs   | n<=c & c=length xs     
        
A: snat x snat x array        
     
\Down (ER list_rel) mop_list_push
>=        
\Down R1 (mop_list_push xs a = xs@[a])
>=
dyn_array_push        
>=hnr A
push_impl        



Side-Problem (verschieben):
- Amortisierte DS von Basic Layer in NREST hochziehen



# Di 19.5.


- Review Projektverlauf
- evtl nur asymptotische schranke für intro_sort_aux (wegen AkkraBazzi/Master-Theorem), dann bringt fein-granulares time-reasoning z.b. bei sift-down wenig...
- Ziel: introsort_time : O(n log n)


## Introsort
- introsort
  - heap sort: n log n beweisen/annehmen
  - introsort_aux: rekurrenz, evtl AkkraBazzi
- insertion_sort
  - äußere schleife linear of length O(|xs|*threshold)
  - inneres sort_one_more_spec in O(threshold)=O(1), i0-1
  - Invarianten zu schwach im Moment! (infos über slices werden aktuell weggeworfen)
  - siehe gen_insertion_sort 

- bei pdqsort
  - introsort ist O(threshold²)=O(threshold*n) mit n=threshold
  
  
## TODO

### Peter
- array mit explizitem ownership into Hnr_Primitives_Experiment
- Abstrakter Teil von Introsort / PDQsort
- Sepref anpassen (sepref_intf, FCOMP...) sobald genügend Sepref_Basis zur Verfügung.

### Max
- NREST eingliedern
- Sepref anpassen


# Do 14.5.

Diskussion zum Thema Zeitanalyse
- Zeitanalyse für Introsort  
  - https://en.wikipedia.org/wiki/Introsort
  - Paper? informeller Beweis?
- PDQ sort
  - Edelkamp et al.
  - Paper über branch aware 
  - Boost implementierung "Orson Peters"  -> blog artikel?
- Paper zu generating worst case inputs for quick sort -> symbolic execution  ???

## TODOs
### Peter
- paper finden, generating worst-case inputs for quicksort mit symbolic execution
- grundlegende hnr_rules beweisen
- Überlegungen zu Laufzeitanalyse sammeln
- evtl beweise mit "counter" die später eingegliedert werden können

### Max
- NREST mit Currencies
- hnr regeln

## nächstes Treffen
- Montag 18.5. 10Uhr UKTime

# Wednesday 13.5.

## Done:
    
  - Introduce GC in generic_wp
    - nötig wegen unterschiedlichen kosten in verschiedenen branches
    - [idee: für constant execution time müsste man überschüssige Zeit "ausleveln"]
  - vcg teilweise anpassen
  - hn_refine definiert + return regel als sanity check bewiesen.
        
## TODO:    
 - Kosten modell direkt über Sepref definieren
   - wahrscheinlich für jede hn_refine regel eine abstrakte currency/währung 
    
### Peter
- fix Frameinference with GC
- Hoaretriples für Basis DS anpassen

### Max
- hnr regeln (bind usw. als sanity check)
- dann: Sepref anpassen
- NREST mit mehr currencies zur verfügung stellen

    
## nächstes treffen: Fr. 15.5. 13uhr UKTime / 14Uhr DeTime

# Monday 11.5.20

## Ideen:
- trace semantic 
  - kann zur rechtfertigung von Zeit und Space benutzt werden. Kompatibel mit ndet.
  trace = lazy list (finite+infinite???, oder finite + NTERM)
  - verifikation von yes()
  -(trace monade)
  - reminds me of a talk by Magnus Myreen (https://drops.dagstuhl.de/opus/volltexte/2019/11087/pdf/LIPIcs-ITP-2019-32.pdf)

  
## TODO:

- bzgl cost_framework:
  - Erweiterungen auf Funtionen, Paare
  - I1-I3: natürlich sprachig verstehen
  - Galois connection conjecture durchdenken

- type class resource_algebra oder so einführen
  - mit x ## y := True
  - dann fällt monoid_add mit sep_algebra zusammen, und man spart sich evtl den datatype acost, welche nur `'a => ('b::monoid_add)` wrapt  
  
- lifting auf Sepref 

### Max
- for_maxX beweisen in Sep_Generic_wp.thy
- algebraische struktur der locale `cost_framework` ausarbeiten
- 

### Peter
- LLVM_Shallow_RS anpassen
- Hoare Triple für basis datenstrukturen beweisen
  - Folder /ds
  - wenns geht: ignore component "TimeFrame Inference module"
  - 
  
## Nächstes Treffen:
Mittwoch 13.5. 10:00 UK-Time / 11:00 DE-Time


# Friday 8.5.20

## design choices:
    
  - kein cc, projektion im abstrakten mit \inf
  - alloc n kostet n
  - free, amortisiert, kostet 1 ! (oder n?)
  -> abstract credits für free in Malloc_Tac aufladen (amortisierung) 
  -> wird von Sepref eingeführt
    
    
# TODO
    
## peter:
  - mono beweise fixen
  - ll_call in code-generator
  - Tupel?
  - bis LLVM_Shallow_RS probleme fixen
    
## max:
  - LLVM_Shallow operationen mit kosten versehen
  - time credits mit top element versehen


# Wednesday 6.5.2020

## Cost Modell

### MRES -> MREST
- erweitern um 'c::{monoid_add}
- Monad.thy anpassen

### LLVM cost modell:
- ops: easy
- controll flow
  - If: easy
  - ll_call: easy, im Code generator aufpassen
  - REC: ll_call in REC', präprozessor mit REC'
  - While: aufpassen! 2 arten code zu generieren.

```
[llvm_inline]: REC' F x = REC (%D x. F (%x. ll_call (D x)) x) x

ll_call (m) = consume 1; m

ll_call (const x y ... z)
```

## TODO:
  
### Max
- Monad.thy weiter anpassen
  - general mres monad
  - mwp 
  - instantiate generic_wp

### Peter
- nada :)

### next steps:
- reasoning infrastruktur
- LLVM specifics

## nächstes treffen:
Do 7.5. nachmittag oder Fr 8.5. 10:00UK/11:00DE

# First Meeting Monday 4.5.2020

## Project Goal:
- proof of concept Sepreft for LLVM mit Zeit
- Use Case: 
  - introsort in O(n log n)
  - stepping stones
    - insertion sort (braucht nur arrays)
    - beleg für orthogonalität von Datenstrukturen und Zeit ? weiterer Use Case
  - secondary goal: Edmonds Karp algorithmus
    - mengen, graphen, 
    - am ende, RBT und matrix by arrays
    
## Steps:
1. Paper Draft + Motivation [Max]
    - https://sharelatex.tum.de/2371529427hwgftpbwgttm
1. Github repo  (start mit original Sepref-LLVM) [Peter]
    - https://github.com/lammich/isabelle_llvm_time
1. Cost model definieren <- zusammen
1. SL + TC bauen <- zusammen
1. Automatisierung für SL+TC = VCG bauen [eher Peter + TC componente von Bohua/Max]
1. Atomare HoareTriple beweisen (blueprint von LLVM) [eher Peter]
1. HNR definieren, Regeln beweisen
1. Introsort/pdqsort example von nres -> nrest
1. Runtime argument kompliziert, [stepping stone insertion sort -> trivial]
1. dokumentieren + ideen weiterspinnen :)
    
    
## Other Topics:
    
### Infrastruktur
  - use NREST mit multi currency    
  - Sepref+Time
  - wieder ein clone, yet another Sepref Clone

Modularitaet: Konkrete Waehrungen sollten den abstrakten Beweis nicht beeinflussen.
 
1. To define: HN_refine
    - mehrere währungen auf mehrere währungen ( die gleichen währungen ? eher nicht),
    - target währungen klar
    - source währungen flexibel 
 
1. Preprocessor bleibt gleich (?!)
 
1. VCG (Basic Layer)
    - solver der art N = M + ?Timeframe
    - Peter's infrastruktur + extra solver für $       
         
1. SL + TC für LLVM
    - enat? "curr => enat"
    - sogar integer TC?
    - modularität erhalten durch aufsplitten von Zeit und Heap. Wie funktioniert Abstraktion von zeit -> sep-algebra-ueber zeit
    
1. Cost model für LLVM
    - atomare operationen easy,
    - control flow ?
    - währung pro OPCode, oder "Schritte"?
    - oder Speicherzugriffe? 
    - Klassen von Waehrungen, zB speicherzugriff = ll_load+ll_store
    - [-> "Kosten" = ZEIT, oder auch SPACE,  MAX_SPACE, (max,curr) ]
  
1. Code Generator bleibt gleich (wirft zeit info weg)
    
### use case
   
introsort, pdqsort and stepping stones
