printf "\nRESUMO";
printf "\nPerdas de potencia ativa (kW)         : %10.2f",sum{(i,j) in ol} (R[i,j]*Iqdr[i,j]); 
printf "\nPerdas de potencia reativa (kVAr)     : %10.2f",sum{(i,j) in ol} (X[i,j]*Iqdr[i,j]); 
printf "\nMagnitude de tensao minima (kV)       : %10.4f(%6.4f pu)",sqrt(min {j in ob} (Vqdr[j])),sqrt(min {j in ob} (Vqdr[j]))/Vnom; 
printf "\nNo da magnitude de tensao minima      : %10d",min{i in ob: Vqdr[i]==min {j in ob} (Vqdr[j])}(i);
printf "\nPotencia ativa da subestacao (kW)     : %10.2f",sum{i in ob: Tb[i] == 1}(PS[i]); 
printf "\nPotencia reativa da subestacao (kVAr) : %10.2f",sum{i in ob: Tb[i] == 1}(QS[i]);
printf "\nPotencia aparente da subestacao (kVA) : %10.2f",sqrt((sum{i in ob: Tb[i] == 1}(PS[i]))^2+(sum{i in ob: Tb[i] == 1}(QS[i]))^2);
printf "\nDemanda de potencia ativa (kW)        : %10.2f",sum{i in ob} (PD[i]); 
printf "\nDemanda de potencia reativa (kVAr)    : %10.2f",sum{i in ob} (QD[i]); 

printf "\n\nMAGNITUDES DE TENSAO (kV)\n No\n";
for {i in ob} {
printf "%4d %8.4f\n",i,sqrt(Vqdr[i]); 
}
printf "\n\nMAGNITUDES DE FLUXO DE CORRENTE (A)\n Circuito\n";
for {(i,j) in ol} {
printf "%4d %4d %8.2f\n",i,j,sqrt(Iqdr[i,j]);
}

printf "\n\nFLUXO DE POTENCIA ATIVA (kW)\n Circuito\n";
for {(i,j) in ol} {
printf "%4d %4d %8.2f\n",i,j,P[i,j];
}

printf "\n\nFLUXO DE POTENCIA REATIVA (kW)\n Circuito\n";
for {(i,j) in ol} {
printf "%4d %4d %8.2f\n",i,j,Q[i,j];
}

printf "\n\nPERDAS DE POTENCIA ATIVA (kW)\n Circuito\n";
for {(i,j) in ol} {
printf "%4d %4d %8.2f\n",i,j,R[i,j]*Iqdr[i,j]; 
}

printf "\n\nFLUXO DE POTENCIA ATIVA NAS CHAVES (kW)\n Chave \n";
for {(i,j) in och} {
printf "%4d %4d %8.2f\n",i,j,Pch[i,j];
}

printf "\n\nFLUXO DE POTENCIA REATIVA NAS CHAVES (kW)\n Chave \n";
for {(i,j) in och} {
printf "%4d %4d %8.2f\n",i,j,Qch[i,j];
}

printf "\n\nCHAVES DE INTERCONEXAO ABERTAS\n Chave \n";
for {(i,j) in och} {
printf "%4d %4d %4d\n",i,j,w[i,j];
}

printf "\n";
printf "\nTotal CPU time:%10.2fs", _ampl_time + _total_solve_time + _total_shell_time;
printf "\nElapsed time :%10.2fs\n", _solve_elapsed_time;