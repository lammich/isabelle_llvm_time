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
