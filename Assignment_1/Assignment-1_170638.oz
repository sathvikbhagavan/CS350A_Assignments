%==================== 1.1 ===================%
declare
fun {Take Xs N}
   if N =< 0 then nil
   else
      case Xs of nil then nil
      []H|T then H|{Take T N-1}
      end
   end
end

{Browse {Take [1 2 3] 1}}


%==================== 1.2 ===================%
declare Last Length ToKElement XsL
fun {Last Xs N}
 
   fun {Length L}
      case L of nil then 0
      []H|T then 1+{Length T}
      end
   end
 
   fun {ToKElement S K}
      if K==0 then S
      else
	 case S of nil then nil
	 []H|T then {ToKElement T K-1}
	 end
      end
   end
  
   XsL={Length Xs}
   if N>=XsL then Xs
   elseif N=<0 then nil
   else {ToKElement Xs XsL-N}
   end
end

{Browse {Last [1 2 3] 2}}

%==================== 1.3 ===================%
declare
fun {Merge Xs Ys}
   case Xs of nil then Ys
   []HX|TX then
      case Ys of nil then Xs
      []HY|TY then
	 if HX =< HY then HX|{Merge TX Ys}
	 else HY|{Merge Xs TY}
	 end
      end
   end
end

{Browse {Merge [1 2 3] [1 2]}}

%==================== 2.1 ===================%
declare
fun {ZipWith BinOp Xs Ys}
   case Xs of nil then nil
   []HX|TX then
      case Ys of nil then nil
      []HY|TY then {BinOp HX HY}|{ZipWith BinOp TX TY}
      end
   end
end

{Browse {ZipWith fun {$ X Y} X+Y end  [1 2 3 4] [4 5 6 4]}}

%==================== 2.2 ===================%
declare
fun {FoldR List Bin Identity}
   case List
   of nil then Identity
   []H|T then {Bin H {FoldR T Bin Identity}}
   end
end


declare
fun {Unary X}
   X+X
end

declare
fun {BinOp U}
   fun {$ H T}
      {U H}|T
   end
end


declare
fun {Map L UnOp}
   {FoldR L {BinOp UnOp} nil}
end

{Browse {Map [1 2 3] Unary}}
   

%==================== 2.3 ===================%
declare
fun {FoldL List BinOp Identity}
   case List of nil then Identity
   []H|T then {FoldL T BinOp {BinOp H Identity}}
   end
end

{Browse {FoldL [1 2 3]  fun {$ X Y} X+Y end 0}}

%==================== 3.1 ===================%
declare
fun {NextTerm X N Prev}
   ~Prev*{Pow X 2.0}/((2.0*N)*(2.0*N+1.0))
end

declare
fun lazy {Sin X N P}
   if N==0.0 then X|{Sin X N+1.0 X}
   else {NextTerm X N P}|{Sin X N+1.0 {NextTerm X N P}}
   end
end

{Browse {Sin 0.523599 0.0 0.0}.2.1}

%==================== 3.2 ===================%
declare
fun {Add X Y}
   X+Y
end

declare
fun {Approximate S Epsilon}
   case S of nil then 0.0
   []H|T then
      if {Abs H-T.1}=<Epsilon then 0.0
      else {Add H {Approximate T Epsilon}}
      end
   end
end

{Browse {Approximate {Sin 0.523599 0.0 0.0} 0.000000001}}

%==================== 4.1 ===================%
declare IsDiagonalRecurse
declare IsRowDiagonal
declare
fun {IsDiagonal M}
   
   fun {IsRowDiagonal L K I}
      case L of nil then true
      []H|T then
	 if {And I==K H\=0} then {IsRowDiagonal T K I+1}
	 elseif {And I\=K H==0} then {IsRowDiagonal T K I+1}
	 else false
	 end
      end
   end

   fun {IsDiagonalRecurse L K P}
      if P==false then false
      else
	 case L of nil then P
	 []H|T then {IsDiagonalRecurse T K+1 {And {IsRowDiagonal H K 0} P}}
	 end
      end
   end

   {IsDiagonalRecurse M 0 true}
end


declare L=[[1 0 0 0] [0 2 0 0] [0 0 1 0] [0 0 0 1]]
{Browse {IsDiagonal L}}



	 

   
   

   

	 
