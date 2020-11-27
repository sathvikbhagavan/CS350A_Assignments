declare SAS = {Dictionary.new}

declare StoreCounter = {NewCell 0}

fun {AddKeyToSAS}
    StoreCounter := @StoreCounter + 1
    {Dictionary.put SAS @StoreCounter equivalence(@StoreCounter)}
    @StoreCounter
end

declare fun {RetrieveFromSAS Key} 
    if {Dictionary.condGet SAS Key ~1} == ~1 
    then ~1
    else {Dictionary.condGet SAS Key ~1}
    end
end

declare fun {GetRoot Key}
    case Key of nil then nil
    else 
        local Val in 
            {Dictionary.get SAS Key Val}
            case Val of equivalence(X) then
                if Key == X then equivalence(Key)
                else {GetRoot X}
                end
            else Val
            end
        end
    end
end

declare proc {BindRefToKeyInSAS Key RefKey}
    local K1 K2 in
        K1 = {GetRoot Key}
        K2 = {GetRoot RefKey}
        case K1 of equivalence(X) then
            case K2 of equivalence(Y) then {Dictionary.put SAS X equivalence(Y)}
            else {Dictionary.put SAS X K2}
            end
        else
            case K2 of equivalence(Y) then {Dictionary.put SAS Y K1}
            else 
                if K1 == K2 then skip
                else {Browse 'Error in BindRefToKeyInSAS'}
                end
            end
        end
    end
end

declare proc {BindValueToKeyInSAS Key Val}
    local X in 
        X = {GetRoot Key}
        case X of equivalence(A) then {Dictionary.put SAS A Val}
        else 
            if X == Val then skip
            else {Browse 'Error in BindValueToKeyInSAS'}
            end
        end
    end
end


            
