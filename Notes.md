

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
