\insert 'Unify.oz'
\insert 'Stack.oz'

declare proc {Interpreter SemStack}
    case @SemStack of nil then {Browse 'Execution completed'}
    [] SemStackElement|_ then
        case SemStackElement.s of nil then 
            SemStack := {Pop @SemStack}
            {Interpreter SemStack}
        [] [nop]|T then
            SemStack := pair(s:T e:SemStackElement.e)|{Pop @SemStack}
            {Interpreter SemStack}
        [] X|Xs then
            % Pattern Matching to various cases : 
            %   1. var ident(X)
            %   2. bind 
            %   3. apply
            case X of var|Y then
                case Y of ident(A)|B then
                    case B of nil then {Browse 'Empty scope of variable'}
                    else 
                        local NewEnv in 
                            {AdjoinAt SemStackElement.e A {AddKeyToSAS} NewEnv}
                            SemStack := pair(s:B e:NewEnv)|pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
                            {Interpreter SemStack}
                        end
                    end
                else {Browse 'Syntax Wrong - Variable name'}
                end
            [] bind|Y then
                {Browse Y}
                case Y of H|T|nil then
                    case H of ident(_) then
                        case T of ident(_) then
                            {Unify H T SemStackElement.e}
                        [] literal(B) then
                            {Unify H B SemStackElement.e}
                            {Browse {Dictionary.entries SAS}}
                            {Browse SemStackElement.e}
                        [] [record literal(_) R] then
                            {Unify H R SemStackElement.e}
                        else {Browse 'Invalid variable/data binding'}
                        end
                    end
                else {Browse 'Syntax wrong'}
                end
            [] match|Y then
                case Y of ident(_)|P|S1|S2|nil then
                    local E in 
                        E = {RetrieveFromSAS SemStackElement.e.X}
                        case E of record|A|F then
                            case P of record|AP|FP then
                                
                    
                        
            SemStack := pair(s:Xs e:SemStackElement.e)|{Pop @SemStack}
            {Interpreter SemStack}
            else {Browse 'Syntax wrong - not a list'}
            end
        else {Browse 'No Pattern Matched'}
        end
    else {Browse 'Something Wrong'}
    end
end

declare proc {ParseInput Input}
    local SemanticStack in
        SemanticStack = {NewCell [pair(s:Input e:env)]}
        {Interpreter SemanticStack}
    end
end

% {ParseInput [[nop] [nop] [nop]]}
% {ParseInput [[nop]]}
% {ParseInput [[nop]]}
% {ParseInput [[var ident(x) [nop]]]}   
% {ParseInput [[var ident(x) [var ident(y) [nop]]] [nop]]}            
% {ParseInput [[var ident(x) [var ident(y) [var ident(x) [nop]]] [nop]]]}
{ParseInput [[var ident(x) [bind ident(x) literal(avi)] [nop]]]}