\insert 'Unify.oz'
\insert 'Stack.oz'
% ------------------------------------
% Authors : Sathvik Bhagavan - 170638
% ------------------------------------
% Semantic Stack is implemented as Cell. It is implemented as:
%   pair(s:Statement e:Environment)



% Adding pattern variables into the environment
declare fun {AddPairs P E}
    case P of nil then E
    []H|T then 
        case H of [literal(_) ident(X)] then
            local NewEnv in
                {AdjoinAt E X {AddKeyToSAS} NewEnv}
                {AddPairs T NewEnv}
            end
        else E
        end
    else E
    end
end

declare fun {PatternVariables P E} 
    case P of [record literal(_) Pairs] then
        {AddPairs Pairs E}
    else E
    end
end


% Computation of free variables and closure
declare fun {CheckFreeVariables S E B F}
    case S of X|Xs then {CheckFreeVariables Xs E B {CheckFreeVariables X E B F}}
    [] ident(X) then 
        if {List.member ident(X) B} then F
        else 
            if {Value.hasFeature F X} then F  
            else 
                if {Value.hasFeature E X} then {AdjoinAt F X E.X}
                else F
                end
            end
        end
    else F
    end
end

declare fun {ComputeClosure S E B F}

    case S of nil then F
    [] [nop] then F
    [] [var ident(X) Xs] then {ComputeClosure Xs E ident(X)|B F}
    [] [bind X Y] then {CheckFreeVariables X E B {CheckFreeVariables Y E B F}}
    [] [match ident(X) P S1 S2] then

        % X is bound case 
        if {List.member ident(X) B} 
        then {ComputeClosure S1 {PatternVariables P E} B {ComputeClosure S2 E B F}}
        else

            % X is already computed to be a free variable
	        if {Value.hasFeature F X} 
            then {ComputeClosure S1 {PatternVariables P E} B {ComputeClosure S2 E B F}} 
	        else

                % X is in the environment - adding it to the free variables
	            if {Value.hasFeature E X} 
                then {ComputeClosure S1 {PatternVariables P E} B {ComputeClosure S2 E B {AdjoinAt F X E.X}}}
	            else E
                end
	        end
	    end
    [] [apply ident(X) P] then

        % X is bound case 
        if {List.member ident(X) B} then {CheckFreeVariables P E B F}
        else

            % X is already computed to be a free variable
	        if {Value.hasFeature F X} then {CheckFreeVariables P E B F} 
	        else

                % X is in the environment - adding it to the free variables
	            if {Value.hasFeature E X} then {CheckFreeVariables P E B {AdjoinAt F X E.X} }
	            else E
	            end
	        end
        end
    [] X|Xs then 
        case Xs of nil then {ComputeClosure X E B F}
        else {ComputeClosure Xs E B {ComputeClosure X E B F}}
        end
    else E
    end
end

% Adding procedure parameters into the environment
declare fun {AddFormalParameters Formal E}
    local AddFormalParametersOne in
        fun {AddFormalParametersOne X E}
            case X of ident(V) then
                {AdjoinAt E V {AddKeyToSAS}}
            else E
            end
        end
        case Formal of nil then E
        [] H|T then {AddFormalParameters T {AddFormalParametersOne H E}}
        end
    end
end


% Procedure to bind given arguements and procedure parameters
declare proc {BindArguementsFormal F A N E}
    case F of nil then skip
    [] HF|TF then 
        case A of HA|TA then
           case HA of ident(K) then
                try 
                    {Unify HF {RetrieveFromSAS E.K} N}
                    {BindArguementsFormal TF TA N E}
                catch _ then 
                    {Browse '[Error] Failed in Unification'}
                end
            end
        end
    end
end

% Check arrity of 2 records to be equal or not
declare fun {CheckArity F G}
    case F of nil then 
        case G of nil then true
        else false
        end
    [] H|T then 
        case G of nil then false
        [] A|B then {And H.1==A.1 {CheckArity T B}}
        end
    end
end
 
% Main Interpreter Procedure
declare proc {Interpreter SemStack}

    % If Semantic Stack is empty -- Execution is over
    case @SemStack of nil then {Browse '[Success] Execution completed'}

    % Non Empty Semantic Stack
    [] SemStackElement|_ then

        % If Statement is nil then that pair is popped out of the Stack
        case SemStackElement.s of nil then 
            SemStack := {Pop @SemStack}
            {Interpreter SemStack}

        % Non Empty Statement
        % Q.1 nop statement
        [] [nop]|T then
            SemStack := pair(s:T e:SemStackElement.e)|{Pop @SemStack}
            {Interpreter SemStack}

        % For other cases
        [] X|Xs then

            % Q.2 var statement
            case X of var|Y then
                case Y of ident(A)|B then
                    case B of nil then skip
                    else 
                        local NewEnv in 

                            % Adding to SAS and then adjoining it to the environment
                            {AdjoinAt SemStackElement.e A {AddKeyToSAS} NewEnv}
                            SemStack := pair(s:B e:NewEnv)|pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                            {Interpreter SemStack}
                        end
                    end
                else {Browse '[Error] var syntax is wrong'}
                end
            
            % Q.3-4 bind statement
            [] bind|Y then
                case Y of H|T|nil then
                    case H of ident(P) then

                        % Variable-Variable binding
                        case T of ident(_) then
                            try
                                {Unify H T SemStackElement.e}
                                SemStack := pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                                {Interpreter SemStack}
                            catch _ then
                                {Browse '[Error] identifier is not instantiated'}
                            end

                        % Variable-Literal binding
                        [] literal(_) then
                            try 
                                {Unify H T SemStackElement.e}
                                SemStack := pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                                {Interpreter SemStack}
                            catch _ then 
                                {Browse '[Error] identifier is not instantiated or already bound to different value'}
                            end

                        % Variable-Record binding
                        [] record|literal(_)|_ then

                            % Check if all the identifiers are instantiated (bounded/unbounded)
                            % Unify only when all are otherwise throw error
                            try
                                {Unify H T SemStackElement.e}
                                SemStack := pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                                {Interpreter SemStack}
                            catch _ then 
                                {Browse '[Error] some/all identifiers in Record are not instantiated'}
                            end

                        % Variable-Procedure binding
                        % Using procedure instead of proc as it is a keyword in Oz
                        [] procedure|Is|S then
                            local CE V Val in 

                                % Computing contextual environment
                                CE = {ComputeClosure S.1 SemStackElement.e Is env}
                                V = [procedure Is S.1 CE]
                                Val = {RetrieveFromSAS SemStackElement.e.P}

                                % Binding the procedure defintion and contextual environment - Closure
                                case Val of equivalence(P) then
                                    {BindValueToKeyInSAS P V}
                                else {Browse '[Error] identifier is already bound'}
                                end
                                SemStack := pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                                {Interpreter SemStack}
                            end
                        else {Browse '[Error] invalid data/identifier/procedure binding'}
                        end
                    else {Browse '[Error] invalid data/identifier/procedure binding'}
                    end
                else {Browse '[Error] bind syntax is wrong'}
                end
            
            % Q.5 match statement
            [] match|Y then
                case Y of ident(A)|P|S1|S2|nil then
                    local E in

                        % Get the record from SAS
                        E = {RetrieveFromSAS SemStackElement.e.A}
                        case E of ~1 then {Browse '[Error] identifier not found'}
                        [] equivalence(_) then {Browse '[Error] identifier unbound'}
                        else 

                            % Pattern Match the record
                            case E of record|N1|G then
                                case P of record|N2|F then
                                    if N1 == N2 then
                                        local L in
                                            if {CheckArity F.1 G.1} then

                                                % Add the pattern variables in the environment
                                                L = {NewCell nil}
                                                L := SemStackElement.e
                                                for T in F.1 do
                                                    case T.2.1 of ident(Z) then
                                                        L := {AdjoinAt @L Z {AddKeyToSAS}}
                                                    [] literal(_) then {Browse 'literal in record'}
                                                    else
                                                        {Browse '[Error] record syntax in pattern match is incorrect'}
                                                    end
                                                end
                                                {Unify ident(A) P @L}
                                                SemStack := pair(s:S1 e:@L)|pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                                                {Interpreter SemStack}
                                                {Browse '[Success] Pattern matched'}
                                            else 

                                                % Pattern did not match
                                                {Browse '[Success] Arity does not match'}
                                                SemStack := pair(s:S2 e:SemStackElement.e)|pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                                                {Interpreter SemStack}
                                            end  
                                        end
                                    else 
                                        {Browse '[Success] name of record is not matching'}
                                        SemStack := pair(s:S2 e:SemStackElement.e)|pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                                        {Interpreter SemStack}
                                    end
                                else {Browse '[Error] p in pattern match is not a record'}
                                end
                            else {Browse '[Error] identifier for pattern match is not a record'}
                            end
                        end
                    end
                else 
                    {Browse '[Error] match syntax is wrong'}
                end
            
            % Q.6 apply statement
            [] apply|Y then
                case Y of ident(F)|Arguements then
                    local Val in 
                        Val = {RetrieveFromSAS SemStackElement.e.F}
                        case Val of equivalence(_) then {Browse '[Error] procedure not bounded'}
                        [] [procedure Formal S CE] then 
                            if {List.length Arguements} \= {List.length Formal} then
                                {Browse '[Error] incorrect number of arguements'}
                            else 
                                local NewEnv in 
                                    NewEnv = {AddFormalParameters Formal CE}
                                    {Browse NewEnv}
                                    {BindArguementsFormal Formal Arguements NewEnv SemStackElement.e}
                                    {Browse SemStackElement.e}
                                    SemStack := pair(s:S e:NewEnv)|{Pop @SemStack}
                                    {Interpreter SemStack}
                                end
                            end
                        else {Browse '[Error] syntax wrong procedure'}
                        end
                    end
                else {Browse '[Error] syntax wrong apply'}
                end
            else {Browse '[Error] syntax wrong list'}
            end
        else {Browse '[Error] syntax wrong pattern matching'}
        end
    else {Browse '[Error] syntax wrong pattern matching'}
    end
end

declare proc {ParseAST Input}
    local SemanticStack in
        SemanticStack = {NewCell [pair(s:Input e:env)]}
        {Interpreter SemanticStack}
    end
end


% Test Cases for the Interpreter


% {ParseAST [[nop] [nop] [nop]]}
% {ParseAST [[nop]]}
% {ParseAST [[nop]]}
% {ParseAST [[var ident(x) [nop]]]}   
% {ParseAST [[var ident(x) [var ident(y) [nop]]] [nop]]}            
% {ParseAST [[var ident(x) [var ident(y) [var ident(x) [nop]]] [nop]]]}
% {ParseAST [[var ident(x) [var ident(y) [bind ident(x) literal(a)] [bind ident(y) ident(x)] [var ident(z) [bind ident(z) ident(x)]]]]]}
% {ParseAST [[var ident(x) [var ident(y) [var ident(z) [bind ident(z) [record literal(a) [[literal(f1) ident(x)] [literal(f2) ident(y)]]]]]] ]]}
% {ParseAST [[var ident(x) [bind ident(x) literal(3)][match ident(x) literal(3) [[nop]] [[nop] [nop]]]]]}
% {ParseAST [[var ident(x) [bind ident(x) [record literal(a) [[literal(1) literal(first)] [literal(2) literal(second)]]]] [match ident(x) [record literal(a) [[literal(1) literal(first)] [literal(2) literal(second)]]] [[nop]] [[nop] [nop]]]]]}
% {ParseAST [[var ident(x) [bind ident(x) literal(a)] [var ident(y) [bind ident(x) [procedure [ident(a) ident(b)] [[bind ident(b) ident(a)]]]]]]]}

% {ParseAST [[var ident(b) [var ident(a) [var ident(x) [bind ident(x) 
%             [record literal(label) [[literal(f1) ident(a)] [literal(f2) ident(b)]]]]
%             [match ident(x) 
%             [record literal(label) [[literal(f1) ident(a)] [literal(f2) ident(b)]]] [[nop] [nop]] [[nop] [nop]]]]]]]}


% {ParseAST [[var ident(x) 
% [bind ident(x) [procedure [ident(x1)] [[bind ident(x1) literal(a)]]]] 
% [var ident(z) [var ident(y) [apply ident(x) ident(y)]]]]]}

{ParseAST [[var ident(y) [var ident(x) [bind ident(x) 
[procedure [ident(x1)] [[nop] [bind ident(x1) ident(y)] [bind ident(x1) literal(a)]]]]
[apply ident(x) ident(y)]]]]}


{Browse '--------------SAS--------------'}
{Browse {Dictionary.entries SAS}}
