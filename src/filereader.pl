:- use_module(library(readutil)). % read_file_to_string/3
:- use_module(library(pcre)). % re_replace/4
:- current_prolog_flag(argv, Args), ( (memberchk(silent, Args) ; memberchk('--silent', Args) ; memberchk('-s', Args))
                                      -> assertz(silent(true)) ; assertz(silent(false)) ).
:- dynamic working_dir/1.
:- dynamic active_metta_load/2.
:- dynamic metta_source_functions_started/1.

push_working_dir(Filename) :- file_directory_name(Filename, Dir0),
                              ( absolute_file_name(Dir0, Dir, [file_type(directory), file_errors(fail)])
                                -> true
                                 ; Dir = Dir0 ),
                              asserta(working_dir(Dir)).

pop_working_dir :- retract(working_dir(_)), !.
pop_working_dir.

%Read Filename into string S and process it (S holds MeTTa code):
load_metta_file(Filename, Results) :- load_metta_file(Filename, Results, '&self').
load_metta_file(Filename, Results, Space) :- catch(load_metta_file_impl(Filename, Results, Space),
                                                   Error,
                                                   rethrow_metta_file_error(Filename, Error)).

load_metta_file_impl(Filename, Results, Space) :-
    absolute_file_name(Filename, CanonPath, [access(read), file_errors(fail)]),
    setup_call_cleanup(
        assertz(active_metta_load(Space, CanonPath), Ref),
        load_metta_file_contents(CanonPath, Results, Space),
        erase(Ref)
    ).

load_metta_file_contents(CanonPath, Results, Space) :-
    claim_source_compile(CanonPath, Mode),
    setup_call_cleanup(
        push_working_dir(CanonPath),
        ( read_file_to_string(CanonPath, S, []),
          process_metta_string(S, Results, Space, file(Mode, CanonPath)) ),
        pop_working_dir
    ).

claim_source_compile(CanonPath, space_only) :-
    metta_source_functions_started(CanonPath), !.
claim_source_compile(CanonPath, compile_functions) :-
    assertz(metta_source_functions_started(CanonPath)).

%Name the file in an error that carries no context of its own (unbound, or a
%bare tag such as typecheck). Any other context - context/2, a stack-overflow
%dict, a predicate indicator - is the thrower's and is rethrown unchanged:
rethrow_metta_file_error(Filename, error(Type, Context)) :- ( var(Context) ; atom(Context) ), !,
                                                            throw(error(Type, context(Filename, 'while loading MeTTa file'))).
rethrow_metta_file_error(_, Error) :- throw(Error).

%Extract function definitions, call invocations, and S-expressions part of &self space:
process_metta_string(S, Results) :- process_metta_string(S, Results, '&self').
process_metta_string(S, Results, Space) :-
    process_metta_string(S, Results, Space, compile_functions).
process_metta_string(S, Results, Space, LoadMode) :- string_codes(S, Cs),
                                                 strip(Cs, 0, Codes),
                                                 phrase(top_forms(Forms, 1), Codes),
                                                 maplist(parse_form, Forms, ParsedForms),
                                                 source_processing_mode(LoadMode, ParsedForms, Mode, File),
                                                 process_parsed_forms(Space, Mode, File, ParsedForms, 1, ResultsList), !,
                                                 append(ResultsList, Results).

register_function_signature(F, Arity) :- warn_if_used_as_symbol(F),
                                         register_fun(F),
                                         ( catch(arity(F, Arity), _, fail) -> true ; assertz(arity(F, Arity)) ).

%A function arriving after expressions already compiled its name as a plain symbol
%cannot be called by those expressions anymore, which usually means an import came too late:
warn_if_used_as_symbol(F) :- \+ fun(F), symbol_head(F), !,
                             format(user_error, "Warning: ~w is defined or imported after already being used; earlier expressions treat it as a plain symbol. Move the import or definition above the first use.~n", [F]).
warn_if_used_as_symbol(_).

%First pass to convert MeTTa to Prolog Terms and register functions:
parse_form(form(S), parsed(T, S, Term)) :- sread(S, Term),
                                           ( Term = [=, [F|W], _], atom(F) -> length(W, N),
                                                                              Arity is N + 1,
                                                                              register_function_signature(F, Arity),
                                                                              T=function
                                                                            ; T=expression ).
parse_form(runnable(S), parsed(runnable, S, Term)) :- sread(S, Term).

%Second pass to compile / run / add the Terms:
process_form(Space, _, parsed(expression, _, Term), []) :- 'add-atom'(Space, Term, true),
                                                        ( silent(true) -> true ; swrite(Term,STerm),
                                                                                 format("\e[33m--> metta sexpr -->~n\e[36m~w~n", [STerm]),
                                                                                 format("\e[33m^^^^^^^^^^^^^^^^^^^~n\e[0m") ).
process_form(_, _, parsed(runnable, FormStr, Term), Result) :- translate_expr([collapse, Term], Goals, Result),
                                                            ( silent(true) -> true ; format("\e[33m--> metta runnable  -->~n\e[36m!~w~n\e[33m-->  prolog goal  -->\e[35m ~n", [FormStr]),
                                                                                     forall(member(G, Goals), portray_clause((:- G))),
                                                                                     format("\e[33m^^^^^^^^^^^^^^^^^^^^^^^~n\e[0m") ),
                                                            call_goals(Goals).
process_form(Space, Mode, parsed(function, FormStr, Term), []) :- Term = [=, [F|_], _],
                                                            %Under the lock definition removals take, as in add-atom:
                                                            with_mutex(petta_definitions,
                                                                       ( load_function_row(Space, Mode, Term, RowRef, Compile),
                                                                         ( Compile == true -> translate_clause(Term, Clause),
                                                                         assertz(Clause, Ref),
                                                                         assertz(translated_from(Ref, Term)),
                                                                         assertz(compiled_row(RowRef, Ref)),
                                                                         capture_clause_display(Ref, Display)
                                                                         ; Display = silent ) )),
                                                            ( Compile == true -> notify_function_changed(F) ; true ),
                                                            ( Display == silent -> true ; Display = clause(Show),
                                                                                     format("\e[33m--> metta function -->~n\e[36m~w~n\e[33m--> prolog clause -->~n\e[32m", [FormStr]),
                                                                                     portray_clause(current_output, Show),
                                                                                     format("\e[33m^^^^^^^^^^^^^^^^^^^^^^~n\e[0m") ).
process_form(_, _, In, _) :- format(atom(Msg), "failed to process form: ~w", [In]), throw(error(syntax_error(Msg), none)).

% Copy the printable clause while its reference is protected. Formatting runs
% after the lock is released and must not dereference a concurrently erased clause.
capture_clause_display(Ref, Display) :-
    ( silent(true) -> Display = silent
    ; clause(Head, Body, Ref), ( Body == true -> Show = Head ; Show = (Head :- Body) ),
      Display = clause(Show) ).

%Like blanks but counts newlines:
newlines(C0, C2) --> blanks_to_nl, !, {C1 is C0+1}, newlines(C1,C2).
newlines(C, C) --> blanks.

%Collect characters until all parentheses are balanced (depth 0), accumulating codes, and also counting newlines:
grab_until_balanced(D, Acc, Cs, LC0, LC2, InS) --> [C],
    ( { InS = 1, C = 0'\\ } -> [E], { ( E=10 -> LC1 is LC0+1 ; LC1 = LC0 ) },
                               grab_until_balanced(D, [E, C|Acc], Cs, LC1, LC2, 1)
    ; { ( C=0'" -> InS1 is 1-InS ; InS1 = InS ),
        ( InS = 0 -> ( C=0'( -> D1 is D+1
                     ; C=0') -> D1 is D-1
                              ; D1 = D )
                   ; D1 = D ),
        Acc1=[C|Acc],
        ( C=10 -> LC1 is LC0+1 ; LC1 = LC0 ) },
      ( { D1=:=0, InS1=0 } -> { reverse(Acc1,Cs) , LC2 = LC1 }
                            ; grab_until_balanced(D1,Acc1,Cs,LC1,LC2,InS1) ) ).

%Read a balanced (...) block if available, turn into string, then continue with rest, ignoring comments:
top_forms([],_) --> blanks, eos.
top_forms([Term|Fs], LC0) --> newlines(LC0, LC1),
                              ( "!" -> {Tag = runnable} ; {Tag = form} ),
                              ( "(" -> [] ; string_without("\n", Rest), { format(atom(Msg), "expected '(' or '!(', line ~w:~n~s", [LC1, Rest]), throw(error(syntax_error(Msg), none)) } ),
                              ( grab_until_balanced(1, [0'(], Cs, LC1, LC2, 0)
                                -> { true } ; string_without("\n", Rest), { format(atom(Msg), "missing ')', starting at line ~w:~n~s", [LC1, Rest]), throw(error(syntax_error(Msg), none)) } ),
                              { string_codes(FormStr, Cs), Term =.. [Tag, FormStr] },
                              top_forms(Fs, LC2).

%Strip off code that is commented out, while tracking when inside of string:
strip([], _, []).
strip([0'\\, C|R], 1, [0'\\, C|O]) :- !, strip(R, 1, O).
strip([0'"|R], 0, [0'"|O]) :- !, strip(R, 1, O).
strip([0'"|R], 1, [0'"|O]) :- !, strip(R, 0, O).
strip([0'\n|R], In, [0'\n|O]) :- !, strip(R, In, O).
strip([0';|R], 0, Out) :- !, (append(_, [0'\n|Rest], R) -> strip(Rest, 0, Out) ; Out = []).
strip([C|R], In, [C|O]) :- strip(R, In, O).

function_form_text(parsed(function, Text, _), Text).

% A file form has one compiled definition, shared by its imported copies.
% The exact source text distinguishes a changed form at the same file position.
source_processing_mode(file(Initial, File), Forms, Mode, File) :- !,
    ( Initial == space_only, file_definition_missing(File, Forms)
      -> Mode = compile_functions ; Mode = Initial ).
source_processing_mode(Mode, _, Mode, none).
file_definition_missing(File, Forms) :-
    nth1(Index, Forms, Form), function_form_text(Form, Text),
    \+ live_source_clause(source(File, Index, Text), _), !.
process_parsed_forms(_, _, _, [], _, []).
process_parsed_forms(Space, Mode, File, [Form|Forms], Index, [Result|Results]) :-
    ( File == none -> FormMode = Mode
    ; function_form_text(Form, Text) -> FormMode = source(File, Index, Text)
    ; FormMode = Mode ),
    process_form(Space, FormMode, Form, Result), Next is Index + 1,
    process_parsed_forms(Space, Mode, File, Forms, Next, Results).

% This runs under the definition lock. A re-import links its row to existing
% code; a missing definition is compiled again, without duplicating survivors.
load_function_row(Space, Mode, Term, RowRef, Compile) :-
    Term = [=, [F|Args], _], length(Args, N), Arity is N + 1,
    register_function_signature(F, Arity),
    add_sexp(Space, Term, RowRef),
    ( Mode = source(File, Index, Text)
      -> Key = source(File, Index, Text),
         ( live_source_clause(Key, Ref)
           -> assertz(compiled_row(RowRef, Ref)), Compile = false
         ; Compile = true ),
         assertz(source_row(Key, RowRef))
    ; Mode == space_only -> Compile = false
    ; Compile = true ).
live_source_clause(Key, Ref) :-
    source_row(Key, RowRef), clause(_, true, RowRef),
    compiled_row(RowRef, Ref), clause(_, _, Ref), !.
