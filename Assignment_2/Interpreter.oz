\insert 'Unify.oz'
\insert 'Stack.oz'

declare proc {Interpreter SemStack}
    % {Browse @SemStack}
    local NewEnv in
        case @SemStack of nil then {Browse 'Execution Completed'}
        [] StackElement|_ then
            case StackElement.s of nil then SemStack := {Pop @SemStack} {Interpreter SemStack}
            [] [nop] then SemStack:={Pop @SemStack} {Interpreter SemStack}
            [] [nop]|T then SemStack:= pair(s:T e:StackElement.e)|{Pop @SemStack} {Interpreter SemStack}
            [] [var|ident(X)|S] then
                {Browse S}
                NewEnv = {AdjoinAt StackElement.e {AddKey} X}
                SemStack := pair(s:S e:NewEnv)|{Pop @SemStack}
                {Browse @SemStack}
                % {Browse {Dictionary.keys SAS}}
                {Interpreter SemStack}
            [] var|ident(X)|S then
                {Browse S}
                NewEnv = {AdjoinAt StackElement.e {AddKey} X}
                SemStack := pair(s:S e:NewEnv)|{Pop @SemStack}
                {Browse @SemStack}
                % {Browse {Dictionary.keys SAS}}
                {Interpreter SemStack}
            else {Browse 'Skipped'}
            end
        end
    end
end

declare proc {ParseInput Input}
    local SemanticStack in
        SemanticStack = {NewCell [pair(s:Input e:env)]}
        {Interpreter SemanticStack}
    end
end

% {ParseInput [[nop] [nop] [nop]]}
% {ParseInput [nop]}
% {ParseInput [[nop]]}
% {ParseInput [[var ident(x) [nop]]]}   
% {ParseInput [[var ident(x) [var ident(y) [nop]]] [nop]]}            
{ParseInput [var ident(x) [var ident(y) [var ident(x) [nop]]] [nop]]}