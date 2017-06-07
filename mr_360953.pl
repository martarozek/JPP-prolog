% Marta Rożek 360953

% Automat to lista stanów. Każdy stan to lista akcji: reduce, shift lub accept.

% item(Nieterminal, PrzedKropką, PoKropce)
% state(Numer, Produkcje/Itemy)

:- use_module(library(lists)).

% accept(+Automat, +Słowo)
accept(Auto, Word) :-
    append(Word, ['#'], HashedWord),
    parse([0], Auto, HashedWord).

% parse(+Stos, +Automat, +Słowo)
% słowo ma dodany znak '#' na końcu
parse([S | _], Auto, ['#']) :-
    member(state(S, Rules), Auto),
    member(accept, Rules),
    !.
parse([S | Stack], Auto, Word) :-
    member(state(S, Rules), Auto),
    member(reduce(NT, Count), Rules),
    popStack([S | Stack], Count, NewStack),
    parse(NewStack, Auto, [nt(NT) | Word]).
parse([S | Stack], Auto, [W | Word]) :-
    member(state(S, Rules), Auto),
    member(shift(W, NewState), Rules),
    parse([NewState, S | Stack], Auto, Word).

% createLR(+Gramatyka, -Automat, -Info)
% Jeśli udało się stworzyć automat, Info ma wartość yes. W p.p. Info to
% konflikt(Opis), a Automat to null.
createLR(gramatyka(Start, Prods), Rules, yes) :-
    getStates(gramatyka(Start, Prods), States),
    statesToRules(States, States, Prods, [], Rules),
    conflicts(Rules, no).
createLR(gramatyka(Start, Prods), null, konflikt(X)) :-
    getStates(gramatyka(Start, Prods), States),
    statesToRules(States, States, Prods, [], Rules),
    conflicts(Rules, konflikt(X)).

% popStack(+Stos, +Ile, -NowyStos)
% NowyStos to Stos ze zrzuconymi Ile obiektami ze szczytu.
popStack(R, 0, R).
popStack([_ | Stack], N, R) :-
    N \= 0,
    N1 is N - 1,
    popStack(Stack, N1, R).

% closure(+Zbiór, +Reguły, -DomkniętyZbiór)
% DomkniętyZbiór jest domknięciem zbioru Zbiór, na podstawie Reguł gramatyki.
closure(X, Rules, X) :- closureIter(X, Rules, X, X).
closure(Items, Rules, Closure) :-
    closureIter(Items, Rules, Items, C),
    Items \= C,
    closure(C, Rules, Closure).

% closureIter(+Zbiór, +Reguły, +Akumulator, -PrawieDomkniętyZbiór)
% PrawieDomkniętyZbiór to domknięcie Zbioru po jednej iteracji algorytmu, które
% może jeszcze nie osiągnęło punktu stałego.
closureIter([], _, R, R).
closureIter([I | Items], Rules, Acc, Closure) :-
    I \= item(_, _, [nt(_) | _]),
    !,
    closureIter(Items, Rules, Acc, Closure).
closureIter([I|Items], Rules, Acc, Closure) :-
    I = item(_, _, []),
    !,
    closureIter(Items, Rules, Acc, Closure).
closureIter([I|Items], Rules, Acc, Closure) :-
    I = item(_, _, [nt(L) | _]),
    !,
    getProdForNT(L, Rules, Prod),
    prodToItems(Prod, [], GenItems),
    append(Acc, GenItems, NewAcc),
    remove_dups(NewAcc, NewAccPruned),
    closureIter(Items, Rules, NewAccPruned, Closure).

% prodToItems(+Produkcje, +Akumultor, -Itemy)
% Itemy to produkcje wyrażone w notacji item.
prodToItems(prod(_, []), R, R).
prodToItems(prod(L, [R | Rs]), Acc, Items) :-
    prodToItems(prod(L, Rs), [item(L, [], R) | Acc], Items).

% getProdForNT(+Nieterminal, +Reguły, -Produkcje)
% Produkcje to prawe strony produkcji dla Nieterminala w Regułach.
getProdForNT(NT, [prod(NT, Prod) | _], prod(NT, Prod)).
getProdForNT(NT, [prod(X,_) | Rules], Prod) :-
    X \= NT,
    getProdForNT(NT, Rules, Prod).

% successor(+Itemy, +Symbol, -Następnik)
% Następnik to zbiór, do którego nastąpi przejście po Symbolu ze stanu
% który zawiera Itemy. Nie jest domknięty.
successor(Items, Symbol, R) :-
    getItemsForSymbol(Items, Symbol, [], MatchingItems),
    moveDot(MatchingItems, [], R).

% successor(+Itemy, +Symbol, +Reguły, -Następnik)
% Następnik to zbiór, do którego nastąpi przejście po Symbolu ze stanu
% który zawiera Itemy. Jest domknięty.
successorClosure(Items, Symbol, Rules, R) :-
    successor(Items, Symbol, SuccItems),
    closure(SuccItems, Rules, R).

% getItemsForSymbol(+ZbiórItemów, +Symbol, +Akumulator, -PasująceItemy).
% PasująceItemy to te itemy ze ZbioruItemów, które po kropce mają Symbol.
getItemsForSymbol([], _, R, R).
getItemsForSymbol([I | Items], Symbol, Acc, R) :-
    I \= item(_, _, [Symbol | _]),
    !,
    getItemsForSymbol(Items, Symbol, Acc, R).
getItemsForSymbol([I | Items], Symbol, Acc, R) :-
    I = item(_, _, [Symbol | _]),
    !,
    getItemsForSymbol(Items, Symbol, [I | Acc], R).

% moveDot(+Itemy, +Akumulator, +PrzesunięteItemy)
% PrzesunięteItemy to Itemy, którym została przesunięta kropka o jeden w lewo.
moveDot([], R, R).
moveDot([I | Items], Acc, R) :-
    I = item(L, Before, [X | After]),
    append(Before, [X], NewBefore),
    moveDot(Items, [item(L, NewBefore, After) | Acc], R).

% getNextSymbolsForItems(+Itemy, +Akumulator, -Symbole)
% Symbole to wszystkie pierwsze symbole po kropce w Itemach.
getNextSymbolsForItems([], R, R).
getNextSymbolsForItems([I | Items], Acc, R) :-
  I = item(_, _, []),
    !,
    getNextSymbolsForItems(Items, Acc, R).
getNextSymbolsForItems([I | Items], Acc, R) :-
  I = item(_, _, [X | _]),
    !,
    remove_dups([X | Acc], NewAcc),
    getNextSymbolsForItems(Items, NewAcc, R).

% getStates(+Gramatyka, -Stany)
% Stany to zbiory konfiguracyjne dla gramatyki.
getStates(gramatyka(Start, Rules), States) :-
     closure([item('Z', [], [nt(Start)])],
             Rules, ZeroState),
    getNextSymbolsForItems(ZeroState, [], StartSymbols),
     dfs(StartSymbols, Rules, ZeroState, 1,
         [state(0, ZeroState)], _, States).

% dfs(+Symbole, +Reguły, +Itemy, +LicznikStanów, +Odwiedzone,
%     -ZwróconyLicznik, -ZwróconeItemy)
% ZwróconeItemy to wszystkie stany konfiguracyjne wygenerowane przechodąc
% po grafie stanów, zaczynając od Itemów. Symbole to symbole po kropce dla
% Itemów, dla których znaleziono ZwróconeItemy.
dfs([], _, _, Counter, R, Counter, R).
dfs([S|Symbols], Rules, Items, Counter, Visited, RCounter, R) :-
    successorClosure(Items, S, Rules, SuccItems),
    member(state(_, SuccItems), Visited),
    !,
    dfs(Symbols, Rules, Items, Counter, Visited, RCounter, R).
dfs([S|Symbols], Rules, Items, Counter, Visited, RCounter, R) :-
    successorClosure(Items, S, Rules, SuccItems),
    \+ member(state(_, SuccItems), Visited),
    !,
    getNextSymbolsForItems(SuccItems, [], SuccSymbols),
    SuccCounter is Counter + 1,
    dfs(SuccSymbols, Rules, SuccItems, SuccCounter,
        [state(Counter, SuccItems) | Visited], SuccRCounter, SuccR),
    dfs(Symbols, Rules, Items, SuccRCounter, SuccR,
        RCounter, R).

% statesToRules(+Stany, +WszystkieStany, +Produkcje, +Akumulator, -Reguły)
% Reguły to Stany przetłumaczone na konkretne akcje - shift, accept, reduce.
statesToRules([], _, _, R, R).
statesToRules([S | States], AllStates, Prods, Acc, R) :-
    S = state(N, Items),
    itemsToRules(Items, Items, AllStates, Prods, [], R1),
    statesToRules(States, AllStates, Prods,
                  [state(N, R1) | Acc], R).

% itemsToRules(+Itemy, +ObecnyStan, +WszystkieStany, +Produkcje, +Akumulator,
%              -Reguły)
% Reguły to Itemy przetłumaczone na akcje, dla ObecnegoStanu.
itemsToRules([], _, _, _, R, R).
itemsToRules([I|Items], State, States, Prods, Acc, R) :-
    I = item(L, Before, []), % reduce
    L \= 'Z',
    !,
    length(Before, Len),
    itemsToRules(Items, State, States, Prods,
                 [reduce(L, Len) | Acc], R).
itemsToRules([I | Items], State, States, Prods, Acc, R) :-
    I = item('Z', _, []), % accept
    !,
    itemsToRules(Items, State, States, Prods, [accept | Acc], R).
itemsToRules([I|Items], State, States, Prods, Acc, R) :-
    I = item(_, _, [X | _]), % shift/goto
    !,
    successorClosure(State, X, Prods, Successor),
    member(state(N, Successor), States),
    itemsToRules(Items, State, States, Prods,
                 [shift(X, N) | Acc], R).

% conflicts(+Automat, -Info)
% Jeśli jest konflikt w stanach Automatu, Info zawiera konflikt(Opis),
% w p.p Info ma wartość no.
conflicts([], no).
conflicts([state(_,Rule) | Rules], R) :-
    conflict(Rule, no),
    conflicts(Rules, R).
conflicts([state(_,Rule) | _], konflikt(X)) :-
    conflict(Rule, konflikt(X)).

% conflict(Stan, Info)
% Jeśli jest konflikt w Stanie, Info zawiera konflikt(Opis),
% w p.p Info ma wartość no.
conflict([], no).
conflict([accept | Items], R) :-
    conflict(Items, R).
conflict([I|Items], no) :-
    I = reduce(_,_),
    \+ member(reduce(_,_), Items),
    \+ member(shift(_,_), Items).
conflict([I | Items], no) :-
    I = shift(_,_),
    \+ member(reduce(_,_), Items).
conflict([I | Items], konflikt("shift/reduce")) :-
    I = shift(_,_),
    member(reduce(_,_), Items).
conflict([I | Items], konflikt("shift/reduce")) :-
    I = reduce(_,_),
    member(shift(_,_), Items).
conflict([I | Items], konflikt("reduce/reduce")) :-
    I = reduce(_,_),
    member(reduce(_,_), Items).
