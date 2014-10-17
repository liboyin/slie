type exp = A | B | Mix of exp * exp | Var of string
type sufficency = exp * exp
type rule = Rule of sufficency * (sufficency list)

// dict:Map<string,exp> -> e:exp -> exp, where @dict, denoting the dictionary, is the result of unification.
// Maps all unknowns in @e to a stable state. A stable expression is a constant, a variable that is not in the dictionary, or a combination of them.
let rec MapVar (dict:Map<string,exp>) e =
    match e with
    | A | B -> e
    | Mix(e1,e2) -> Mix(MapVar dict e1, MapVar dict e2)
    | Var(key) ->
        let x = dict.TryFind key // x:option<exp>, intermediate result exposed for clarity and debugging.
        match x with
        | Some(value) -> if value=e then e else MapVar dict value // Handles the possibility when the result of dictionary lookup is still unstable.
        | None -> e

// e:exp -> vn:string -> bool, where @vn is the name of variable.
// Tests whether @e contains Var(@vn).
let rec Contains e vn =
    match e with
    | A | B -> false
    | Mix(e1,e2) -> Contains e1 vn || Contains e2 vn
    | Var(vn') -> vn=vn'

// dict:Map<string,exp> -> e1:exp -> e2:exp -> Map<string,exp> option
// @dict is the existing dictionary, @e1 is the fst/snd part of the query sufficiency, and @e2 is the same part of the goal sufficiency.
// Unifies two expressions, adds new mappings to the dictionary, and returns Some(NewDictionary) if unification succeeds, or None if fails.
let rec UnifyExp dict e1 e2 =
    let (x1,x2) = (MapVar dict e1,MapVar dict e2) // Mapps (@e1,@e2) to a stable state.
    match (x1,x2) with // (x1,x2):exp*exp, intermediate result exposed for clarity and debugging.
    | _ when x1=x2 -> Some(dict)
    | (Var(vn),e) | (e,Var(vn)) -> // These two conditions must not be swapped, since @e1 is from the query, and @e2 is from the goal.
        if Contains e vn then None else Some(dict.Add(vn,e)) // If @e contains Var(@vn), unification fails since it leads to an infinite loop. Otherwise, a new mapping is added to the dictionary.
    | (Mix(e1a,e1b),Mix(e2a,e2b)) ->
        let x = UnifyExp dict e1a e2a // x:Map<string,exp> option, intermediate result exposed for clarity and debugging.
        match x with
        | Some(dict') -> UnifyExp dict' e1b e2b
        | None -> None
    | _ -> None // Other forms are not unifiable.

// dict:Map<string,exp> -> s1:(exp*exp) -> s2:(exp*exp) -> Map<string,exp> option
// @s1 is the query sufficiency, @s2 is the goal sufficiency.
// Unifies two sufficiencies.
let UnifySuff dict s1 s2 =
    let x = UnifyExp dict (fst s1) (fst s2)
    match x with
    | Some(dict') -> UnifyExp dict' (snd s1) (snd s2)
    | None -> None

// n:int -> e:exp -> exp, where @n is the recursion depth.
// Normalizes an expression by appending the recursion depth to the end of all variable names.
let rec NormExp n e =
    match e with
    | A | B -> e
    | Mix(e1,e2) -> Mix(NormExp n e1, NormExp n e2)
    | Var(vn) -> Var(vn + string n)

// n:int -> suff:(exp*exp) -> exp*exp.
// Normalizes a sufficiency.
let NormSuff n suff = (NormExp n (fst suff),NormExp n (snd suff))

// n:int -> rule:(exp*exp)*((exp*exp) list) -> (exp*exp)*(exp*exp) list.
// Normalizes a rule.
let NormRule n (Rule(goal,subgoals)) = (NormSuff n goal,List.map (NormSuff n) subgoals)

// ar:rule list -> dict:Map<string,exp> -> queries:sufficency list -> rules:rule list -> depth:int -> bool
// @ar is the list of all rules. It is never changed during execution, and is only used to start solving a new query.
// @queries is the list of unsolved queries, and @rules is the list of rules that have not been checked against @queries.head.
// Solves @queries.head with @rules.head as the rule, and @dict as the dictionary.
let rec Solve ar dict queries rules depth =
    if depth=8 then false else // Recursion depth starts from 0. When it reaches 8, this function fails.
    match queries with
    | [] -> true // @queries list is empty iff all queries have succeeded.
    | query::qTail ->
        match rules with
        | [] -> false // @rules list is empty iff @query have failed all rules.
        | rule::rTail ->
            let (goal,subgoals) = NormRule depth rule // goal:sufficency, subgoals:sufficency list
            let x = UnifySuff dict query goal // x:Map<string,exp> option, intermediate result exposed for clarity and debugging.
            match x with
            | Some(dict') -> // @dict' is the the augmented dictionary if unification succeeded.
                if Solve ar dict' subgoals ar (depth+1) // Try solve @subgoals with all rules and the augmented dictionary.
                then Solve ar dict' qTail ar depth // If succeeded, try solve other queries with all rules and the augmented dictionary.
                else Solve ar dict queries rTail depth // If failed, try solve the same query with other rules and the original dictionary.
            | None -> Solve ar dict queries rTail depth // If the unification failed, try solve the same query with other rules and the original dictionary.

let suffices ruleGens (exp1,exp2) =
    let rules = List.map (fun f -> f()) ruleGens
    Solve rules (Map.empty<string,exp>) [(exp1,exp2)] rules 0

// tests

let newVar v = Var(v)
let newVar2 (v1,v2) = newVar v1, newVar v2
let newVar3 (v1,v2,v3) = newVar v1, newVar v2, newVar v3
let newVar4 (v1,v2,v3,v4) = newVar v1, newVar v2, newVar v3, newVar v4
let rule1() = let x = newVar "x" in Rule ((x, x), [])
let rule2() = let (x1,x2,y) = newVar3("x1","x2","y") in Rule((Mix(x1,x2), y),[(x1,y)])
let rule3() = let (x1,x2,y) = newVar3("x1","x2","y") in Rule((Mix(x1,x2), y),[(x2,y)])
let rule4() = Rule((Mix(A,B),Mix(B,A)),[])
let rule5() = Rule((Mix(B,A),Mix(A,B)),[])
let rule6() = let (x1,x2,y1,y2) = newVar4("x1","x2","y1","y2") in Rule((Mix(x1,x2),Mix(y1,y2)),[(x1,y1);(x2,y2)])
let rule7() = let (x1,x2,y1,y2) = newVar4("x1","x2","y1","y2") in Rule((Mix(x1,x2),Mix(y1,y2)),[(x1,y2);(x2,y1)])
let rule8() = let x = newVar "x" in Rule((x,Mix(x,x)),[])
let rule9() = let (x1,x2,y,z) = newVar4("x1","x2","y","z") in Rule((Mix(x1,x2),y),[(x1,z); (z,y)] )
let rule10() = let (x1,x2,y,z) = newVar4("x1","x2","y","z") in Rule((Mix(x1,x2),y),[(x2,z); (z,y)] )
let rule11() = Rule((A,B),[])
let rule12() = Rule((B,A),[])
let rulesA = [rule1; rule2; rule3; rule6]
let rulesB = [rule1; rule2; rule3; rule4; rule5; rule6; rule7; rule8]
let rulesC = [rule4; rule5; rule9; rule10; rule11; rule12]

[<EntryPoint>]
let main argv =
    let res = suffices rulesA (Mix (A, B), A)
    printfn "%b" res
    0