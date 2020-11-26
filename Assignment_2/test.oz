declare proc {PM A} 
    case A of nil then skip
    [] var|ident(X)|Xs then {Browse Xs}
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