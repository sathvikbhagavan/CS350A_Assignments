declare proc {PM A} 
    case A of nil then skip
    [] var|ident(_)|S then {Browse S}
    else {Browse 'Pattern Not Matching'}
    end
end

{PM [var ident(x) [var ident(y) [var ident(x) [nop]]] [nop]]}

% [] H|T then
%     {Browse H}
%     case H.1 of var then
%         case H.2.1 of ident(X) then 
%             NewEnv = {AdjoinAt StackElement.e {AddKey} X}
%             SemStack := pair(s:H.2.2 e:NewEnv)|pair(s:T e:StackElement.e)|{Pop @SemStack}
%             {Browse {Dictionary.keys SAS}}
%             {Interpreter SemStack} 
%         end
%     end
% [] [bind ident(X) ident(Y)]|T then
%     {Unify ident(X) ident(Y) StackElement.e}
%     SemStack := pair(s:T e:StackElement.e)|{Pop @SemStack}
%     {Interpreter SemStack}
% [] [bind ident(X) Y]|T then
%     {Unify ident(X) Y StackElement.e}
%     SemStack := pair(s:T e:StackElement.e)|{Pop @SemStack}

[var ident(X) S1]|S2 then
            local NewEnv in 
                {AdjoinAt SemStackElement.e X {AddKeyToSAS} NewEnv}
                SemStack := pair(s:S1 e:NewEnv)|pair(s:S2 e:SemStackElement.e)|{Pop @SemStack}
                {Interpreter SemStack}
            end