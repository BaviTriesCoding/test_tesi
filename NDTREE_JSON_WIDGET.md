# NDTree JSON Widget

## Overview
Il widget **NDTreeJsonViewer** permette di visualizzare e controllare il JSON degli alberi di deduzione naturale (NDTree) in modo interattivo.

## Funzionalità

### 1. **Visualizzazione Strutturata**
- Visualizza l'albero NDTree in formato JSON espandibile
- Supporta due modalità di visualizzazione:
  - **Vista Albero**: Mostra il JSON in forma gerarchica collassabile (predefinita)
  - **Vista Raw JSON**: Mostra il JSON formattato in modo leggibile

### 2. **Interazione**
- **Espandi/Collassa**: Clicca su nodi per espandere/collassare sottogruppi
- **Copia JSON**: Copia l'intero albero in JSON negli appunti con un clic
- **Cambio Visualizzazione**: Passa tra vista strutturata e vista raw

### 3. **Supporto del Parsing JSON**
L'NDTree è ora completamente serializzabile e deserializzabile:
```lean
-- Converti NDTree a JSON String
def NDTree.toJsonString (tree : NDTree) : String

-- Visualizza il tipo della radice
def NDTree.rootType : NDTree → String

-- Conta i nodi totali
def NDTree.countNodes : NDTree → Nat

-- Conta foglie aperte
def NDTree.countOpenLeaves : NDTree → Nat

-- Conta foglie chiuse  
def NDTree.countClosedLeaves : NDTree → Nat
```

## RPC Methods

### `getTreeAsJson`
Recupera l'albero di deduzione naturale in formato JSON per una data posizione nel file.

**Parametri:**
- `pos`: Posizione nel file (Lsp.Position)

**Risultato (TreeAsJsonResult):**
- `thmName`: Nome del teorema/dichiarazione
- `thmType`: Tipo della dichiarazione
- `treeJson`: JSON serializzato dell'NDTree

## Struttura NDTree JSON

```json
{
  "leaf": {
    "val": "formula string",
    "val": true/false
  },
  "node": {
    "val": [
      { nested trees... },
      { nested trees... }
    ],
    "val": "formula string", 
    "val": "proof method string"
  },
  "unhandled": {
    "val": "formula string"
  }
}
```

## Widget in Azione

### Sposta il cursore su un teorema
Quando sposti il cursore su una dichiarazione (teorema, assioma, etc.), il widget automaticamente:
1. Esegue una query RPC per ottenere l'NDTree
2. Parsa il JSON e lo visualizza
3. Mostra il nome e il tipo della dichiarazione
4. Permette di navigare e ispezionare l'albero

### Esempio di Output
```
foo2 : A → A

TREE IN JSON

├─ unhandled("")
```

## Definizione del Tipo NDTree

```lean
inductive NDTree where
  | leaf      : String → Bool → NDTree    -- Formula e booleano (aperta/chiusa)
  | node      : List NDTree → Formula → ProofMethod → NDTree  -- Figli, formula, regola
  | unhandled : Formula → NDTree          -- Nodo non gestito
  deriving FromJson, ToJson, Server.RpcEncodable
```

## Utilizzo Pratico

1. Apri un file Lean con teoremi
2. Sposta il cursore su una dichiarazione
3. Il pannello NDTreeJsonViewer mostra il JSON
4. Usa i pulsanti per:
   - Cambiare visualizzazione
   - Copiare l'intera struttura JSON
5. Espandi/collassa i nodi per navigare l'albero

## Note Tecniche

- Il widget è implementato in React e utilizza l'infrastruttura RPC di Lean
- La serializzazione JSON è automatica grazie a `deriving FromJson, ToJson`
- Il widget supporta alberi di qualsiasi profondità
- Espansione automatica fino a 2 livelli per leggibilità
- Colori sintassi standard VS Code Dark theme
