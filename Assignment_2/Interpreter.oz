\insert 'Unify.oz'
\insert 'Stack.oz'

% Semantic Stack is implemented as Cell. It is implemented as:
%   pair(s:Statement e:Environment)

declare proc {Interpreter SemStack}
    % If Semantic Stack is empty -- Execution is over
    case @SemStack of nil then {Browse 'Execution completed'}

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
                    case B of nil then {Browse 'No Statement to execute'}
                    else 
                        local NewEnv in 

                            % Adding 'A' to SAS and then adjoining it to the environment
                            {AdjoinAt SemStackElement.e A {AddKeyToSAS} NewEnv}
                            SemStack := pair(s:B e:NewEnv)|pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                            {Interpreter SemStack}

                        end
                    end
                else {Browse 'var syntax is wrong'}
                end
            
            % Q.3-4 bind statement
            [] bind|Y then
                case Y of H|T|nil then
                    case H of ident(_) then
                        {Browse {Dictionary.entries SAS}}
                        
                        % Variable-Variable binding
                        case T of ident(_) then
                            {Unify H T SemStackElement.e}
                            SemStack := pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                            {Interpreter SemStack}

                        % Variable-Literal binding
                        [] literal(_) then
                            {Unify H T SemStackElement.e}
                            SemStack := pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                            {Interpreter SemStack}

                        % Variable-Record binding
                        [] record|_ then
                            {Unify H T SemStackElement.e}
                            SemStack := pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                            {Interpreter SemStack}

                        % Variable-Procedure binding
                        % [] [pro R S] then

                        
                        else {Browse 'Invalid variable/data binding'}
                        end
                    end
                else {Browse 'bind syntax wrong'}
                end
            
            % match statement
            [] match|Y then
                case Y of ident(X)|P|S1|S2|nil then
                    local E in 
                        E = {RetrieveFromSAS SemStackElement.e.X}
                        case E of record|A|F then
                            case P of record|AP|FP then
                                try 
                                    local L in
                                        L = {NewCell nil}
                                        L := SemStackElement.e
                                        for T in F.1 do
                                            case T.2.1 of ident(A) then
                                                L := {AdjoinAt @L X {AddKeyToSAS}}
                                            else
                                                {Browse 'ident(A) not matching'}
                                            end
                                        end
                                        {Unify ident(X) P @L}
                                        SemStack := pair(s:S1 e:@L)|pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                                        {Interpreter SemStack}
                                    end
                                catch _ then
                                    SemStack := pair(s:S2 e:SemStackElement.e)|pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                                    {Interpreter SemStack}
                                end
                            else {Browse 'Pattern did not match for P'}
                            end
                        else {Browse 'X is not a record'}
                        end
                    end
                else {Browse 'match syntax wrong'}
                end
            
            % [] apply|Y then
            %     case Y of ident(F)|V then

            else {Browse 'Syntax wrong - not a list'}
            end
        else {Browse 'No Pattern Matched'}
        end
    else {Browse 'Something Wrong'}
    end
end

declare proc {ParseAST Input}
    local SemanticStack in
        SemanticStack = {NewCell [pair(s:Input e:env)]}
        {Interpreter SemanticStack}
    end
end

declare ListMember FilterElements UniqueElements CalcFreeVariablesBind CalcFreeVariables

fun {ListMember E L} 
    {List.member E L}
end

fun {FilterElements H T}
    case T of nil then nil
    []H1|T1 then
        if H1==H then {FilterElements H T1}
        else H1|{FilterElements H T1}
        end
    end
end

fun {UniqueElements L}
    case L of nil then nil
    []H|T then H|{FilterElements H {UniqueElements T}}
    end
end

fun {CalcFreeVariablesBind S}
    case S of nil then nil
    [] pro|V|S1 then {CalcFreeVariables S1 V}
    [] H|T then {UniqueElements {Append {CalcFreeVariablesBind H} {CalcFreeVariablesBind T}}}
    [] ident(_) then [S]
    else nil
    end
end

fun {CalcFreeVariables Statement FreeVariables}
    local G H in 
        case Statement of nil then G=nil
        [] [nop] then G=nil
        [] var|ident(X)|S then G={CalcFreeVariables S {UniqueElements {Append FreeVariables [ident(X)]}}}
        [] bind|S then G={CalcFreeVariablesBind S}
        [] match|X|P|S1|S2|nil then G={UniqueElements {Append {Append {CalcFreeVariables S1 {UniqueElements {Append {CalcFreeVariablesBind P} FreeVariables}}} {CalcFreeVariables S2 FreeVariables}} {CalcFreeVariablesBind X}}}
        [] S1|S2 then G={UniqueElements {Append {FreeVariables S1} {FreeVariables S2}}}
        else {Browse 'Pattern not matching'}
        end
        {List.filter G ListMember _ H}
        H
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
{ParseAST [[var ident(x) [bind ident(x) [record literal(a) [[literal(f1) ident(x1)] [literal(f2) ident(x2)]]]]]]}


{Browse {Dictionary.entries SAS}}
