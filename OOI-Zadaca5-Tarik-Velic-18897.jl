#Tarik Velić 18897
using LinearAlgebra

#goal min/max
#A matrica koeficijenata s lijeve strane ograničenja
#b vektor slobodnih koeficijenata ograničenja [1 x n]
#c vektor koeficijenata u funckiji cilja [1 x n]
#csigns znakovi ograničenja [1 x n]
#vsigns znakovi promjenljivih [1 x n]
function general_simplex(goal, c, A, b, csigns = nothing, vsigns = nothing)  
    if vsigns === nothing
        vsigns = zeros(Int, 1, size(c)[2])
        for i=1:size(vsigns)[2]
            csigns[i] += 1
        end
    end 
    if csigns === nothing
        csigns = ones(Int, 1, size(b)[2])
        if goal == "max"
            for i=1:size(csigns)[2]
                csigns[i] += 1
                csigns[i] *= -1
            end
        end
    end 
    if (size(c)[2] != size(A)[2] || size(b)[2] != size(A)[1] || size(csigns)[2]!=size(A)[1] || size(vsigns)[2]!=size(A)[2] || !(goal == "min" || goal == "max"))
        return NaN, nothing, nothing, nothing, nothing, 5 
    end
    for i=1:size(csigns)[2]
        if (!(csigns[i] == -1 || csigns[i] == 1 || csigns[i] == 0))
            return NaN, nothing, nothing, nothing, nothing, 5 
        end
    end
    for i=1:size(vsigns)[2]
        if (!(vsigns[i] == -1 || vsigns[i] == 1 || vsigns[i] == 0))
            return NaN, nothing, nothing, nothing, nothing, 5 
        end
    end
    pocetni_broj_promjenljivih = size(c)[2]
    status = 0
    b = transpose(b)
    csigns = transpose(csigns) 
    vsigns = transpose(vsigns) 
    indeksi_dodanih_zbog_neogranicenosti = Vector{Int}()
    negativne_promjenljive = Vector{Int}() #indeksi promjenljivih koje će se na kraju množiti sa -1
    neogranicene_po_znaku = Tuple{Int, Int}[] #čuvanje podataka o pormjenljivim koje će se dobiti kao xi'-xi'' (zbog ograničenja =)
    for i = 1:size(vsigns)[1]
        if (vsigns[i] < 0) #ako je znak neke promjenljive <=, kolona njenih koeficijenata množi se sa -1
            push!(negativne_promjenljive, i)
            for j = 1:size(A)[1]
                A[j, i] *= -1
            end
            c[i] *= -1 #vrijednost koeficijenta u funckiji cilja također se množi sa -1
        elseif (vsigns[i] == 0) #ako je ograničenje bilo = dodaje se nova kolona i čuva se podatak kako će se kasnije dobiti vrijednost odgovarajuće promjenljive
            nova_kolona = -A[:, i]
            A = [A nova_kolona]
            novi_element = -c[i] 
            c = [c novi_element] #u funkciju cilja također dodajemo novi element jednak negiranoj vrijednosti kritičnog
            indeks_nove_kolone = size(A)[2]
            push!(neogranicene_po_znaku, (i, indeks_nove_kolone)) 
            push!(indeksi_dodanih_zbog_neogranicenosti, indeks_nove_kolone)
        end
    end
    for i =1:size(b)[1]
        if (b[i] < 0) #ako je neki od koeficijenta bi negativan, čitavo ograničenje se množi sa -1
            A[i, :] *= -1
            b[i] *= -1
            csigns[i] *= -1
        end
    end
    broj_dodatnih_kolona = 0
    for i=1:size(csigns)[1]
        if (csigns[i] == 1) broj_dodatnih_kolona += 2
        else broj_dodatnih_kolona += 1
        end
    end
    A = [A zeros(size(A)[1], broj_dodatnih_kolona)] #dodajemo kolone tako da odgovara ukupnom broju promjenljivih koje ćemo imati
    indeksi_dopunskih = Vector{Int}()
    indeksi_vjestackih = Vector{Int}()
    indeksi_vjestackih_za_izbacivanje = Vector{Int}()
    baza = Vector{Int}()
    broj_promjenljivih = size(c)[2]
    spregnute = Vector{Int}()
    for i=1:size(A)[1] #priprema koeficijenata dopunskih i vještačkih za simpleks; pamćenje koje su dopunske a koje vještačke
        if (csigns[i] == -1)
            broj_promjenljivih += 1
            A[i, broj_promjenljivih] = 1
            push!(spregnute, broj_promjenljivih)
            push!(indeksi_dopunskih, broj_promjenljivih)
            push!(baza, broj_promjenljivih)
        elseif (csigns[i] == 0)
            broj_promjenljivih += 1
            A[i, broj_promjenljivih] = 1
            push!(spregnute, broj_promjenljivih)
            push!(indeksi_vjestackih, broj_promjenljivih)
            push!(baza, broj_promjenljivih)
        elseif (csigns[i] == 1)
            broj_promjenljivih += 2
            A[i, broj_promjenljivih - 1] = -1
            A[i, broj_promjenljivih] = 1
            push!(spregnute, broj_promjenljivih - 1)
            push!(indeksi_dopunskih, broj_promjenljivih - 1)
            push!(indeksi_vjestackih, broj_promjenljivih)
            push!(indeksi_vjestackih_za_izbacivanje, broj_promjenljivih) # u slučaju kada je ograničenje tipa = ne izbacujemo vještačku iz rješenja, pa ih zato razdvajamo
            push!(baza, broj_promjenljivih)
        end
    end
    A = [A b; zeros(2, broj_promjenljivih + 1)] #M će biti u zadnjem redu, Z u predzadnjem
    if (goal == "max") #popunjavamo Z red
        for i=1:size(c)[2]
            A[size(b)[1]+1, i] = c[i]
        end
    elseif (goal == "min")
        for i=1:size(c)[2]
            A[size(b)[1]+1, i] = -c[i]
        end
    end
    for j=1:size(A)[2] #popunjavamo M red
        suma = 0
        for i=1:size(b)[1]
            if (csigns[i] != -1 && !(j in indeksi_vjestackih))
                suma += A[i, j]
            end
        end
        A[size(A)[1], j] = suma
    end
    T = A
    min = 1000000
    red = 0
    # stavljamo 0.00000001 jer nekad umjesto 0 ispadnu pozitivni ali jako mali brojevi, pa algoritam ne može da terminira
    while (maximum(T[size(T)[1], setdiff(1:size(T)[2]-1, indeksi_vjestackih)]) > 0.00000001 || maximum(T[size(T)[1] - 1, setdiff(1:size(T)[2]-1, indeksi_vjestackih)]) > 0.00000001) # Provjera da li u zadnjem redu (bez zadnje kolone) ima elemenata > 0
        maxk = maximum(T[size(T)[1], setdiff(1:size(T)[2]-1, indeksi_vjestackih)])
        redZ = false
        if all(x -> !(x in baza), indeksi_vjestackih) 
            redZ = true
            maxk = maximum(T[size(T)[1] - 1, setdiff(1:size(T)[2]-1, indeksi_vjestackih)]) #ako u redu M nema pozitivnih, uzimamo iz reda Z
        end
        row, col = size(T) 
        if (redZ)
            last_row = T[row - 1, 1:col-1] # Predposljednji red bez posljednje kolone (red Z)
        else 
            last_row = T[row, 1:col-1] # Posljednji red bez posljednje kolone (red M)
        end
        if redZ
            kandidati = findall(x -> x == maxk, last_row)
            kolona = rand(kandidati)
            while kolona in indeksi_vjestackih #Znamo da sigurno postoji odgovarajući kandidat koji nije vještačka promjenljiva
                kolona = rand(kandidati)
            end
        else
            kandidati = findall(x -> x == maxk, last_row)
            if length(kandidati) == 1
                kolona = kandidati[1]
            elseif length(kandidati) > 1
                predzadnji_red = T[row - 1, kandidati]
                # Pronalazak indeksa kolone sa maksimalnim elementom iz predzadnjeg reda
                max_iz_predzadnjeg, indeks_max_iz_predzadnjeg = findmax(predzadnji_red)
                # Ako ima više "najvećih", odaberi random
                indeksi_najvecih = findall(x -> x == max_iz_predzadnjeg, T[row - 1, 1:size(T)[2]-1])
                kolona = indeksi_najvecih[rand(1:end)]
                while kolona in indeksi_vjestackih #Znamo da sigurno postoji odgovarajući kandidat koji nije vještačka promjenljiva
                    kolona = indeksi_najvecih[rand(1:end)]
                end
            end
        end
        for i = 1:size(T)[1]-2
            if (T[i, kolona] > 0 && T[i, size(T)[2]] / T[i, kolona] <= min)
                if (T[i, size(T)[2]] / T[i, kolona] == min)
                    red = rand([red; i]) #slucajni odabir promjenljive koja izlazi iz baze ako ima vise mogucnosti
                else
                    red = i
                end
                min = T[i, size(T)[2]] / T[i, kolona]
            end
        end

        if min != 1000000
            baza[red] = kolona
        else
            return Inf, nothing, nothing, nothing, nothing, 3
        end

        #Priprema simplex tabele za iducu iteraciju

        if T[red, kolona] != 1
            T[red, :] .= T[red, :] ./ T[red, kolona]
        end

        for i = 1:size(T)[1]
            if i != red
                T[i, :] = (-T[i, kolona] * T[red, :]) + T[i, :]
            end
        end

        min = 1000000
    end
    if any(x -> x in baza, indeksi_vjestackih)
        return NaN, nothing, nothing, nothing, nothing, 4
    end
    if any(x -> x == 0, T[1:size(T)[1]-2, size(T)[2]])
        status = 1
    end
    x = zeros(1, size(T)[2] - 1) # rjesenje za sve x-eve (osim vjestackih)
    for i = 1:size(baza)[1]
        x[1, Int(baza[i])] = T[i, size(T)[2]]
    end
    if !isempty(negativne_promjenljive)
        # Pomnoži odgovarajuće elemente u vektoru x sa -1 (za promjenljive čiji znak je bio <=0)
        x[negativne_promjenljive] .= -x[negativne_promjenljive]
    end
    x = vec(x)
    for par in neogranicene_po_znaku # dobijanje promjenljivih koje su bile neograničene po znaku
        indeks_x, indeks_za_izbacivanje = par
        x[indeks_x] -= x[indeks_za_izbacivanje]
    end
    indeksi_za_izbacivanje = union(indeksi_dodanih_zbog_neogranicenosti, indeksi_vjestackih_za_izbacivanje)
    novi_indeksi = setdiff(1:length(x), indeksi_za_izbacivanje)

    # Kreiranje novog vektora bez elemenata koji su dodani zbog neograničenosti po znaku
    x = x[novi_indeksi]
    cilj = -1 * T[size(T)[1] - 1, size(T)[2]]
    if (goal == "min") 
        cilj *= -1
    end
    if any(x -> x>=0 && x <= size(T)[2] - 1 && T[size(T)[1] - 1, x] == 0 && !(x in baza) && !(x in indeksi_vjestackih) && !(x in indeksi_dodanih_zbog_neogranicenosti), 1:size(T)[2]-1)
        status = 2
    end
    izvorniY = zeros(1, size(spregnute)[1]) 
    dopunskiY = zeros(1, pocetni_broj_promjenljivih) 
    for i=1:size(izvorniY)[2]
        value = T[size(T)[1]-1, spregnute[i]]
        if goal == "min"
            if csigns[i] == 1
                value *= -1
            end
        elseif goal == "max"
            if csigns[i] != 1
                value *= -1
            end
        end

        izvorniY[i] += value
    end
    for i=1:size(dopunskiY)[2]
        dopunskiY[i] = T[size(T)[1]-1, i]
        dopunskiY[i] *= -1
    end
    izvorniX = x[1:pocetni_broj_promjenljivih]
    dopunskiX = x[pocetni_broj_promjenljivih+1:end]
    return cilj, izvorniX, dopunskiX, izvorniY, dopunskiY, status 
    
end

# PRIMJERI IZ PREDAVANJA

#=
Zadatak 1: (predavanje 4, str. 14)
Očekivani izlaz:
x1 = 6, x2 = 3, x3 = 0, x4 = 12 i x5 = 0
y1 = 2, y2 = 0, y3 = 1, y4 = 0 i y5 = 0
Z = 36
=#
goal="max";
c=[5 2];
A=[1 0; 0 2; 3 2];
b=[6 18 24] 
csigns=[-1 -1 -1] 
vsigns=[1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#=
Zadatak 2: (predavanje 4, str. 17)
Očekivani izlaz:
x1 = 0, x2 = 0, x3 = 500/7, x4 = 300/7, x5 = 0, x6 = 0
y1 = 24/7, y2 = 30/7, y3 = 1/7, y5 = 9/70, y7 = 0 i y9 = 0
Z = 1860/7
=#
goal="max";
c=[0.2 0.3 3 1.2];
A=[0.1 0 0.5 0.1; 0 0.1 0.3 0.2];
b=[40 30] 
csigns=[-1 -1] 
vsigns=[1 1 1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#=
Zadatak 3: (predavanje 4, str. 20)
Očekivani izlaz:
x1 = 2, x2 = 6, x3 = 2, x4 = 0, x5 = 0, x6 = 1, x7 = 16
y1 = 0, y2 = 3/2, y3 = 1, y4 = 0, y5 = 0, y6 = 0, y7 = 0
Z = 36
=#
goal="max";
c=[3 5];
A=[1 0; 0 2; 3 2; 1 3; 2 3];
b=[4 12 18 21 6] 
csigns=[-1 -1 -1 -1 1] 
vsigns=[1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#=
Zadatak 4: (predavanje 4, str. 24)
Očekivani izlaz:
x1 = 1, x2 = 0, x3 = 3, x4 = 0, x5 = 0
y1 = 400, y2 = -100, y3 = 0, y4 = 400, y5 = 0
Z = 700
=#
goal="max";
c=[100 300 200];
A=[1 2 1; 3 1 2];
b=[4 9] 
csigns=[0 0] 
vsigns=[1 1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#=
Zadatak 5:
Očekivani izlaz:
Rješenje je u beskonačnosti.
=#
goal="max";
c=[2 3];
A=[3 -2; -4 6; 2 -3];
b=[5 8 7] 
csigns=[-1 1 -1] 
vsigns=[1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#=
Zadatak 6:
Očekivani izlaz:
Nema rješenja.
=#
goal="min";
c=[2 3];
A=[-4 6; 2 -3];
b=[8 7] 
csigns=[1 1] 
vsigns=[1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#=
Zadatak 7: (predavanje 3, str. 6, dual problema)
Očekivani izlaz: (riješeno pomoću solvera)
x1 = 7.3333, x2 = 1.3333, x3 = 0, x4 = 0, x5 = 4.3333, x6 = 0
y1 = 40, y2 = 0, y3 = 60, y4 = 0, y5 = 0, y6 = 20
Z = 880
=#
goal="min";
c=[100 110 120];
A=[1 2 2; 1 1.5 1; 1 0.5 1];
b=[10 5 8] 
csigns=[1 1 1] 
vsigns=[0 1 -1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

# testovi sa c2

#test1
#Z=3000;  X=(60 20) Xd(90 0 60 100 0 40); Y(0 30 0 0 10 0) Yd(0 0) status(0)
goal="max";
c=[40 30];
A=[3 1.5;1 1;2 1;3 4;1 0;0 1];
b=[300 80 200 360 60 60] 
csigns=[-1 -1 -1 -1 -1 -1] 
vsigns=[1  1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#**********************************************************************
#test2
#Z=12;  X=(12 0) Xd(14 4 0); Y(0 0 1) Yd(0 0.5); status(0)
goal="min";
c=[1 1.5];
A=[2 1; 1 1; 1 1];
b=[10 8 12] 
csigns=[1 1 1] 
vsigns=[1  1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#**********************************************************************
#test3
#Z=38;  X=(0.66 0 0.33 0) Xd(0 0 0.3 0.16); Y(2 0.12 0 0) Yd(0 36 0 34); status(0)
goal="min";
c=[32 56 50 60];
A=[1 1 1 1;250 150 400 200;0 0 0 1;0 1 1 0];
b=[1 300 0.3 0.5] 
csigns=[0 1 -1 -1] 
vsigns=[1  1 1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#**********************************************************************
#dual prethodnog problema
#test4
#Z=38; X(2 0.12 0 0) Xd(0 36 0 34); Y=(0.66 0 0.33 0) Yd(0 0 0.3 0.16);  status(0)
goal="max";
c=[1 300 -0.3 -0.5];
A=[1 250 0 0;1 150 0 -1;1 400 0 -1;1 200 -1 0];
b=[32  56  50  60] 
csigns=[-1 -1 -1 -1] 
vsigns=[0  1 1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#**********************************************************************
#test5
#Z=Inf; Problem ima neograniceno rjesenje (u beskonacnosti); status(3)
goal="max";
c=[1 1];
A=[-2 1;-1 2];
b=[-1 4] 
csigns=[-1 1] 
vsigns=[1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#**********************************************************************
#test6
#Z=Nan; Dopustiva oblast ne postoji; status(4)
goal="max";
c=[1 2];
A=[1 1; 3 3];
b=[2 4] 
csigns=[1 -1] 
vsigns=[1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#**********************************************************************
#test7
#Z=12*10^6; X(2500 1000) Xd(1500 0 0 2000); Y(0 2000 0 0) Yd(0 0); status(2)
#Z=12*10^6; X(2000 2000) ; status(2)
goal="max";
c=[4000 2000];
A=[3 3;2 1;1 0;0 1];
b=[12000 6000 2500 3000] 
csigns=[-1 -1 -1 -1] 
vsigns=[1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")

#**********************************************************************
#test8
#Z=18; X(0 2) Xd(0 0); Y(0 4.5) Yd(1.5 0); status(1)
#Z=18; X(0 2) Xd(0 0); Y(1.5 1.5) Yd(0 0); status(1)
goal="max";
c=[3 9];
A=[1 4;1 2];
b=[8 4] 
csigns=[-1 -1] 
vsigns=[1 1] 
Z,X,Xd,Y,Yd,status=general_simplex(goal,c,A,b,csigns,vsigns)
println("Z = ", Z)
println("X = ", X)
println("Xd = ", Xd)
println("Y = ", Y)
println("Yd = ", Yd)
println("status = ", status)
println("--------------------")