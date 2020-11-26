declare fun {Push S key}
    key|S
end

declare fun {Top S}
    S.1
end

declare fun {Pop S}
    case S of nil then nil
    []_|T then T
    end
end
