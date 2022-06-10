***For Corn/Cotton***
**See this link regarding the natural gas required to pump one acre land:  https://www.farmprogress.com/farm-profits-squeezed-both-ends

***https://journals.sagepub.com/doi/pdf/10.1177/1536867X0400400407
*Check this link for unbalanced panel




************************************************************
*****1. Restricted Normalized Translog Profit Function******
************************************************************
clear all
set more off

*For corn
import excel "C:\Users\spath11\OneDrive - Louisiana State University\New Translog\Submit to Irrigation Science\Revise and Resubmit Irri Sci\R&R_11_9_2021\Data and codes\2_data_final.xlsx", sheet(corn) firstrow clear
rename t avg_temp
rename dday29_sum t
rename corn_acreage a
keep if a>1000

*For cotton
import excel "C:\Users\spath11\OneDrive - Louisiana State University\New Translog\Submit to Irrigation Science\Revise and Resubmit Irri Sci\R&R_11_9_2021\Data and codes\2_data_final.xlsx", sheet(cotton) firstrow clear
rename t avg_temp
rename dday32_sum t
rename cotton_acreage a
keep if a>1000

*1.Defining the variables*
     **(rainfall and temperature are exogenous environmental inputs in production of corn and cotton)
     **(fertilizer, irrigation and labor are variable inputs of crop and cotton production)
	 **(all costs and profit are calculated on per acre basis.)
label variable yr"Year"
label variable county"County"
label variable fips"FIPS Code"
label variable region"Region"
label variable q"Quantity of Output Produced Per Acre"
label variable p"Price of output"
label variable r"Rainfall"
label variable tmin"Avg. Minimum Temperature"
label variable tmax"Avg. Maximum Temperature"
label variable avg_tem"Average Temperature"
label variable pg"Price of natural gas"
label variable t"Degree days above threshold during crop growing season"
label variable pf"Price of Fertilizer per pound" 
label variable pw"Price of Water per acre-inch"
label variable pl"Price of Labor per hour"
label variable w"Quantity(inch) of Water per acre"
label variable l"Quantity(hours) of Labor"

*Variable costs and profit (Use these two commands only for simulated data.)
gen vc = (f*pf) + (w*pw) + (l*pl) //Total variable costs
gen y = q*p - vc //Restricted profit 
label variable vc"Variable Cost"  
***///Variable cost includes costs of of three inputs: fertilizer, water and labor
label variable y"Restricted Profit" 
***///Restricted profit is obtained by subtracting variable cost from crop revenue.



****Normalization
global varlist "pf pw pl y"
foreach var of global varlist{
    gen n`var' = `var'/p
}
*Label normalized variables
label variable npf"Normalized Fertilizer Price"
label variable npw"Normalized Water Price"
label variable npl"Normalized Labor Price"
label variable ny"Normalized Profit"

*Generate logarithms of variables 
global loglist "npf npw npl ny"
foreach var of global loglist{
    gen l`var' = ln(`var')
}

gen lnr = ln(r) //Log of rainfall
gen lnt = ln(t) // Log of temperature
gen ff = 1/2*lnpf*lnpf
gen ww = 1/2*lnpw*lnpw 
gen ll = 1/2*lnpl*lnpl
gen rr = 1/2*lnr*lnr 
gen tt = 1/2*lnt*lnt
gen fw = lnpf*lnpw 
gen fl = lnpf*lnpl 
gen fr = lnpf*lnr
gen ft = lnpf*lnt
gen wl = lnpw*lnpl 
gen wr = lnpw*lnr 
gen wt = lnpw*lnt 
gen lr = lnpl*lnr 
gen lt = lnpl*lnt 
gen rt = lnr*lnt 

*Share of input and output 
gen shoutput = -q/ny //Share of output 
gen shf = -f*npf/ny 
gen shw = -w*npw/ny
gen shl = -l*npl/ny 

label variable shoutput"Share of Output"
label variable shf"Share of Fertilizer"
label variable shw"Share of Water"
label variable shl"Share of Labor"
**Share value of inputs are made negative to facilitate regression model as in equation (2) of Sidhu and Baanante (1981), American Journal of Agricultural Economics

*Check if summation = 1
gen sum_1 = shoutput-(shf+shw+shl)
sum sum_1

***Other variable specifications:
     *Dependent variable: lny=log of normalized profit
     *Independent variables: lnf=log of normalized fertilizer price; lnw= log of normalized water price; lnl= log of normalized labor wage
              ** lnr= log of mean annual rainfall; lnt= log of mean annual temperature
              ** hff= 1/2*(lnf*lnf); hww= 1/2*(lnw*lnw); hll=1/2*(lnl*lnl); hrr: 1/2*(lnr*lnr); htt:1/2*(lnt*lnt)
              ** fw = lnf*lnw; fl= lnf*lnl; wl= lnw*lnl; fr= lnf*lnr; ft= lnf*lnt; wr= lnw*lnr
              ** wt= lnw*lnt; lr= lnl*lnr; lt= lnt*lnt; rt= lnr*lnt

*For figure of factor cost shares***
gen ferti_cost_share = f*pf/vc
gen water_cost_share = w*pw/vc
gen labor_cost_share = l*pl/vc			  
			  
****Descriptive statistics of different variables***
sum r t q p f pf w pw l pl vc y a
asdoc sum r t q p f pf w pw l pl vc y, dec(2) replace  //ssc install asdoc to obtain word file.
****Descriptive statistics of input and output shares***(simply ignore the negative sign here)
sum shoutput shf shw shl
asdoc sum shoutput shf shw shl, dec(2) replace 
***Descriptive statistics of log of normalized inputs***
sum lnpf lnpw lnpl lnr lnt

*Share of irrigation cost to revenue:
gen irri_share = (w*pw)/(q*p) 
summarize irri_share 
return list 
scalar mean = r(mean)
scalar sd = r(sd)
scalar cv = (sd/mean)*100
display cv //Coefficient of variation

**Definining equation**
global profit "(lny lnpf lnpw lnpl ff ww ll fw fl wl fr ft wr wt lr lt rr tt rt lnr lnt i.yr i.fips)"  //Also check with regional, and county dummies.
global fertilizer "(shf lnpf lnpw lnpl lnr lnt i.yr i.fips)"
global water "(shw lnpf lnpw lnpl lnr lnt i.yr i.fips)"
global labor "(shl lnpf lnpw lnpl lnr lnt i.yr i.fips)"
**To avoid singularity, we avoid "global output equation" in iterated SURE procedure.

**Imposing symmetry constraints to the model for consistent parameter estimates**
constraint define 1 [shf]lnpw=[lny]fw
constraint define 2 [shw]lnpf=[lny]fw
constraint define 3 [shf]lnpl=[lny]fl
constraint define 4 [shl]lnpf=[lny]fl
constraint define 5 [shw]lnpl=[lny]wl
constraint define 6 [shl]lnpw=[lny]wl
constraint define 7 [shf]lnpf=[lny]ff
constraint define 8 [shw]lnpw=[lny]ww
constraint define 9 [shl]lnpl=[lny]ll
constraint define 10 [shf]lnr=[lny]fr
constraint define 11 [shf]lnt=[lny]ft
constraint define 12 [shw]lnr=[lny]wr
constraint define 13 [shw]lnt=[lny]wt
constraint define 14 [shl]lnr=[lny]lr
constraint define 15 [shl]lnt=[lny]lt
constraint define 16 [shf]_cons=[lny]lnpf
constraint define 17 [shw]_cons=[lny]lnpw
constraint define 18 [shl]_cons=[lny]lnpl
*Note: We do not need to impose homogeneity because it is automatically imposed with use of normalized specifications*

**Running Iterated SURE Procedure for Unrestricted/Unconstrained Model**
sureg $profit $fertilizer $water $labor, isure corr
estimates store full 
disp e(ll)

**Iterated SURE Procedure for Restricted Model**
sureg $profit $fertilizer $water $labor, constr(1-18) isure corr
      *(small is not used in sureg equation due to big dataset; We need Z-stat not t-statistics here)*

**"lrtest" compares constrained model with the previously stored unconstrained model**
*(full is the unconstrained model and '.' is the constrained model)*
lrtest full .
*Display log likelihood of the function*
disp e(ll)


**Generate Scalar Values of Variables for Use in Elasticity Equations***
sum lnr
return list
scalar rbar = r(mean)  
**////rbar is the mean value of log of annual rainfall
sum lnt
return list
scalar tbar = r(mean)  
**////tbar is the mean value of log of annual temperature
sum lnpf
return list 
scalar fbar = r(mean)   
**/////fbar is the mean value of log of normalized fertilizer price
sum lnpw 
return list
scalar wbar = r(mean)  
**/////wbar is the mean value of log of normalized water price
sum lnpl
return list
scalar lbar = r(mean)   
**/////lbar is the mean value of log of normalized labor wage
sum sho
return list
scalar shobar = r(mean) 
**//////shobar is the mean value of Output share
sum shf
return list
scalar shfbar = r(mean) 
**//////shfbar is the mean value of Fertilizer share
sum shw
return list 
scalar shwbar = r(mean) 
**//////shwbar is the mean value of Water share
sum shl
return list
scalar shlbar = r(mean) 
**///////shlbar is the mean value of Labor share

***Calculate Elasticity of Inputs and Output Supply along with delta Standard Error***
   **Own Price Elasticity ==> ff= Fertilizer demand with respect to(w.r.t) Fertilizer price; ww= Water demand w.r.t Water price; ll=Labor demand w.r.t Labor wage; yy= Output supply w.r.t. Output price
   **Cross Price Elasticity ==> fw= Fertilizer demand w.r.t Water Price; fl= Fertilizer demand w.r.t. Labor Wage; fr= Fertilizer demand w.r.t. Rainfall
             *                  ft= Fertilizer demand w.r.t. Temperature; fy= Fertilizer demand w.r.t. Output price
			 *					wf= Water demand w.r.t Fertilizer price; wl= Water demand w.r.t. Labor wage; wr= Water demand w.r.t. Rainfall
             *                  wt= Water demand w.r.t. Temperature; wy= Water demand w.r.t. Output price
			 * 				    lf= Labor demand w.r.t Fertilizer price ; lw= Labor demand w.r.t. Water price; lr= Labor demand w.r.t. Rainfall
             *                  lt= Labor demand w.r.t. Temperature; ly= Labor demand w.r.t. Output price
			 *				    yf= Output supply w.r.t Fertilizer Price; yw= Output supply w.r.t Water price; yl= Output supply w.r.t Labor wage
			 *					yt= Output supply w.r.t Temperature; yr= Output supply w.r.t Rainfall

nlcom (ff:-(-(shfbar))-1-(-(_b[ff])/(-shfbar)))(ww:-(-(shwbar))-1-(-(_b[ww])/(-shwbar)))(ll:-(-(shlbar))-1-(-(_b[ll])/(-shlbar)))(fw:-(-(shwbar))-(-(_b[fw])/(-shfbar))) ///
       (fl:-(-(shlbar))-(-(_b[fl])/(-shfbar)))(wf:-(-(shfbar))-(-(_b[fw])/(-shwbar)))(wl:-(-(shlbar))-(-(_b[wl])/(-shwbar)))(lf:-(-(shfbar))-(-(_b[fl])/(-shlbar))) ///
	   (lw:-(-(shwbar))-(-(_b[wl])/(-shlbar)))(fy:-(shobar)+(-(_b[ff])-(_b[fw])-(_b[fl]))/(-shfbar))(wy:-(shobar)+(-(_b[ww])-(_b[fw])-(_b[wl]))/(-shwbar)) ///
	   (ly:-(shobar)+(-(_b[ll])-(_b[fl])-(_b[wl]))/(-shlbar))(fr:-(_b[lnr])-(_b[fr]*fbar)-(_b[rr]*rbar)-(_b[rt]*tbar)-(-(_b[fr])/(-shfbar))) ///
	   (wr:-(_b[lnr])-(_b[wr]*wbar)-(_b[rr]*rbar)-(_b[rt]*tbar)-(-(_b[wr])/(-shwbar)))(lr:-(_b[lnr])-(_b[lr]*lbar)-(_b[rr]*rbar)-(_b[rt]*tbar)-(-(_b[lr])/(-shlbar))) ///
	   (ft:-(_b[lnt])-(_b[ft]*fbar)-(_b[tt]*tbar)-(_b[rt]*rbar)-(-(_b[ft])/(-shfbar))) (wt:-(_b[lnt])-(_b[wt]*wbar)-(_b[tt]*tbar)-(_b[rt]*rbar)-(-(_b[wt])/(-shwbar))) ///
	   (lt:-(_b[lnt])-(_b[lt]*lbar)-(_b[tt]*tbar)-(_b[rt]*rbar)-(-(_b[lt])/(-shlbar)))(yf:-(-shfbar)-(-_b[ff]-_b[fw]-_b[fl])/(-shobar))(yw:-(-shwbar)-(-_b[ww]-_b[fw]-_b[wl])/(-shobar)) ///
	   (yl:-(-shlbar)-(-_b[ll]-_b[fl]-_b[wl])/(-shobar))(yr:(-(_b[lnr])-_b[fr]*fbar-_b[wr]*wbar-_b[lr]*lbar-_b[rr]*rbar-_b[rt]*tbar)+((-_b[fr]-_b[wr]-_b[lr])/(-shobar))) ///
	   (yt:(-(_b[lnt])-_b[ft]*fbar-_b[wt]*wbar-_b[lt]*lbar-_b[tt]*tbar-_b[rt]*rbar)+((-_b[ft]-_b[wt]-_b[lt])/(-shobar)))(yy:(-shfbar-shwbar-shlbar)+(-_b[ff]-_b[fw]-_b[fl]-_b[ww]-_b[wl]-_b[ll])/(-shobar))

*Alternatively, please check this new formula:	   
	   nlcom (ff:-(-(shfbar))-1-((_b[ff])/(-shfbar)))(ww:-(-(shwbar))-1-((_b[ww])/(-shwbar)))(ll:-(-(shlbar))-1-((_b[ll])/(-shlbar)))(fw:-(-(shwbar))-((_b[fw])/(-shfbar))) ///
       (fl:-(-(shlbar))-((_b[fl])/(-shfbar)))(wf:-(-(shfbar))-((_b[fw])/(-shwbar)))(wl:-(-(shlbar))-((_b[wl])/(-shwbar)))(lf:-(-(shfbar))-((_b[fl])/(-shlbar))) ///
	   (lw:-(-(shwbar))-((_b[wl])/(-shlbar)))(fy:-(shobar)+((_b[ff])+(_b[fw])+(_b[fl]))/(-shfbar))(wy:-(shobar)+((_b[ww])+(_b[fw])+(_b[wl]))/(-shwbar)) ///
	   (ly:-(shobar)+((_b[ll])+(_b[fl])+(_b[wl]))/(-shlbar))(fr:(_b[lnr])+(_b[fr]*fbar)+(_b[rr]*rbar)+(_b[rt]*tbar)-((_b[fr])/(-shfbar))) ///
	   (wr:(_b[lnr])+(_b[wr]*wbar)+(_b[rr]*rbar)+(_b[rt]*tbar)-((_b[wr])/(-shwbar)))(lr:(_b[lnr])+(_b[lr]*lbar)+(_b[rr]*rbar)+(_b[rt]*tbar)-((_b[lr])/(-shlbar))) ///
	   (ft:(_b[lnt])+(_b[ft]*fbar)+(_b[tt]*tbar)+(_b[rt]*rbar)-((_b[ft])/(-shfbar))) (wt:(_b[lnt])+(_b[wt]*wbar)+(_b[tt]*tbar)+(_b[rt]*rbar)-((_b[wt])/(-shwbar))) ///
	   (lt:(_b[lnt])+(_b[lt]*lbar)+(_b[tt]*tbar)+(_b[rt]*rbar)-((_b[lt])/(-shlbar)))(yf:-(-shfbar)-(_b[ff]+_b[fw]+_b[fl])/(-shobar))(yw:-(-shwbar)-(_b[ww]+_b[fw]+_b[wl])/(-shobar)) ///
	   (yl:-(-shlbar)-(_b[ll]+_b[fl]+_b[wl])/(-shobar))(yr:((_b[lnr])+_b[fr]*fbar+_b[wr]*wbar+_b[lr]*lbar+_b[rr]*rbar+_b[rt]*tbar)+((_b[fr]+_b[wr]+_b[lr])/(-shobar))) ///
	   (yt:((_b[lnt])+_b[ft]*fbar+_b[wt]*wbar+_b[lt]*lbar+_b[tt]*tbar+_b[rt]*rbar)+((_b[ft]+_b[wt]+_b[lt])/(-shobar)))(yy:(-shfbar-shwbar-shlbar)+(_b[ff]+_b[fw]+_b[fl]+_b[ww]+_b[wl]+_b[ll])/(-shobar))
	   

**(Negative signs are used in addition to that specified by the model because we have negated all the......
  *...values of input shares to make regression feasible. Use of additional negative signs ensures that....
  *...input shares are actually positive. The signs of the coefficients also are altered making our........
  *...estimate consistent with the model specified in Sidhu and Baanante (1981-AJAE).
  

**************************************
*Checking for Cobb-Douglas Hypothesis*
**************************************
  *H0= The coefficients of all second order terms in profit equation is zero.
  *H1= The coefficients of at least one second order terms in profit equation is other than zero.
test _b[ff]=_b[fw]=_b[fl]=_b[ww]=_b[wl]=_b[ll]=_b[fr]=_b[ft]=_b[wr]=_b[wt]=_b[lr]=_b[lt]=0


****************************************
*Checking Profit Maximization Condition*
****************************************
  *Validity of symmetry and homegeneity restrictions across profit and share equations.
  *H0:Parameters of the input share equations are equal to the corresponding same parameters on the profit equation.
  *Conduct this test with out constraints in the SURE model.
  *Combine test reject the null hypothesis; however, when done separately failure to reject null can be observed at some conditions.
quietly sureg $profit $fertilizer $water $labor, isure
 test (_b[lny:ff]=_b[shf:lnpf]) (_b[lny:ww]=_b[shw:lnpw])(_b[lny:ll]=_b[shl:lnpl]) ///
	 (_b[lny:fw]=_b[shf:lnpw]=_b[shw:lnpf])(_b[lny:fl]=_b[shf:lnpl]=_b[shl:lnpf]) ///
	 (_b[lny:wl]=_b[shw:lnpl]=_b[shl:lnpw]) ///
     (_b[lny:fr]=_b[shf:lnr]) (_b[lny:ft]=_b[shf:lnt]) ///
	 (_b[lny:wr]=_b[shw:lnr]) (_b[lny:wt]=_b[shw:lnt]) ///
     (_b[lny:lr]=_b[shl:lnr]) (_b[lny:lt]=_b[shl:lnt])
	 
********************
*Monotonicity Check*
********************
 *This check should be run immediately after running the SURE model.
 *The estimated shares must be positive (negative in our case because we have multiplied with negative sign to run the model)
quietly sureg $profit $fertilizer $water $labor, constr(1-18) isure corr
predict fhat, equation(shf)
predict what, equation(shw)
predict lhat, equation(shl)

summarize fhat what lhat //Summary of predicted share values. Due to negation of shares during analysis. The -ve value is interpreted as positive and vice-versa.
summarize fhat if fhat<0 //To see how many observations have satisfied monotonicity
summarize what if what<0 //To see how many observations have satisfied monotonicity
summarize lhat if lhat<0 //To see how many observations have satisfied monotonicity


***************************
*Checking Returns to Scale*
***************************
test (_b[lny:lnpf]+_b[lny:lnpw]+_b[lny:lnpl]=1)(_b[lny:ff]+_b[lny:fw]+_b[lny:fl]=0) (_b[lny:ww]+_b[lny:fw]+_b[lny:wl]=0) (_b[lny:ll]+_b[lny:fl]+_b[lny:wl]=0)

***********************************************
*Convexity check (Based on Baum and Litz, 2009)
***********************************************
generate double h11 = _b[lny:ff] + shf^2 - shf
generate double h21 = _b[lny:fw] + shf * shw
generate double h31 = _b[lny:fl] + shf * shl
generate double h22 = _b[lny:ww] + shw^2 - shw 
generate double h23 = _b[lny:wl] + shw * shl 
generate double h33 = _b[lny:ll] + shl * shl
mkmat h*, mat(M)

mata: 
M = st_matrix("M")'
lambda = J(cols(M), 3, .)
for(i = 1; i<=cols(M); i++) {
	mt = invvech(M[., i])
	lambda[i, .] = symeigenvalues(mt)
}
lambda 
end 

mata: mm_matlist(lambda, "%9.5f")
*If positive eigenvalues are present, then the assumption of concavity is not fulfilled, thus convex.


*For figure of factor cost shares***
* gen ferti_cost_share = f*pf/vc
* gen water_cost_share = w*pw/vc
* gen labor_cost_share = l*pl/vc			  
*Do not impose any restriction on acre (e.g. a>1000) and alike to calculate shares.
collapse (mean) ferti_cost_share water_cost_share labor_cost_share, by(yr)

twoway connected ferti_cost_share water_cost_share labor_cost_share yr, subtitle("{it:Corn}") msymbol(x triangle_hollow circle_hollow) lpattern(dash dash_dot longdash) xtitle("{bf:Year}", margin(small)) ytitle("{bf:Cost share proportion}", margin(small)) xlabel(1998(2)2020, angle(45)) ylabel(0 "0" 0.2(0.2)0.8, format(%03.1f)) plotregion(fcolor(white)) graphregion(fcolor(white)) legend(symxsize(*1) size(small) row(1) label(1 "Fertilizers") label(2 "Irrigation water") label(3 "Labor"))


twoway connected ferti_cost_share water_cost_share labor_cost_share yr, subtitle("{it:Cotton}") msymbol(x triangle_hollow circle_hollow) lpattern(dash dash_dot longdash) xtitle("{bf:Year}", margin(small)) ytitle("{bf:Cost share proportion}", margin(small)) xlabel(1998(2)2020, angle(45))ylabel(0 "0" 0.2(0.2)0.8, format(%03.1f)) plotregion(fcolor(white)) graphregion(fcolor(white)) legend(symxsize(*1) size(small) row(1) label(1 "Fertilizers") label(2 "Irrigation water") label(3 "Labor"))
********************************************************************************
*For figure of price of input and output
quietly clear all
quietly set more off
*For corn
import excel "C:\Users\spath11\OneDrive - Louisiana State University\New Translog\Submit to Irrigation Science\Revise and Resubmit Irri Sci\R&R_11_9_2021\Data and codes\2_data_final.xlsx", sheet(corn) firstrow clear
rename t avg_temp
rename dday29_sum t
rename corn_acreage a
keep if a>1000

collapse (mean) p pf pw pl, by(yr)
gen pa = p/4.2*100 //Corn price indexed by 2015 corn price
gen pfa = pf/0.2739667*100 //Fertilizer price indexed by 2015 fertilizer price
gen pwa = pw/5.475*100 //Water price indexed by 2015 water price
gen pla = pl/16.115723*100 //Labor price index by 2015 labor price

twoway connected pfa pwa pla pa yr,  subtitle("{it:Corn}") msymbol(x triangle_hollow circle_hollow diamond_hollow) lpattern(dash dash_dot longdash) xtitle("{bf:Year}", margin(small)) ytitle("{bf:Price index} (2015 = 100)", margin(medium)) ///
xlabel(1998(2)2020, angle(45)) ylabel(40(30)220) plotregion(fcolor(white)) graphregion(fcolor(white)) legend(symxsize(*0.59) size(small) ///
row(1) label(1 "Fertilizer price") label(2 "Irrigation water price") label(3 "Labor wage") label(4 "Output price"))
***************************************************************************************


*For cotton
import excel "C:\Users\spath11\OneDrive - Louisiana State University\New Translog\Submit to Irrigation Science\Revise and Resubmit Irri Sci\R&R_11_9_2021\Data and codes\2_data_final.xlsx", sheet(cotton) firstrow clear
rename t avg_temp
rename dday32_sum t
rename cotton_acreage a
keep if a>1000

collapse (mean) p pf pw pl, by(yr)
gen pa = p/0.57*100 //Corn price indexed by 2015 corn price
gen pfa = pf/0.2108982*100 //Fertilizer price indexed by 2015 fertilizer price
gen pwa = pw/7.433*100 //Water price indexed by 2015 water price
gen pla = pl/16.51031*100 //Labor price index by 2015 labor price

twoway connected pfa pwa pla pa yr,  subtitle("{it:Cotton}") msymbol(x triangle_hollow circle_hollow diamond_hollow) lpattern(dash dash_dot longdash) xtitle("{bf:Year}", margin(small)) ytitle("{bf:Price index} (2015 = 100)", margin(medium)) ///
xlabel(1998(2)2020, angle(45)) ylabel(40(30)220) plotregion(fcolor(white)) graphregion(fcolor(white)) legend(symxsize(*0.59) size(small) ///
row(1) label(1 "Fertilizer price") label(2 "Irrigation water price") label(3 "Labor wage") label(4 "Output price"))





*********************************************************************
*************Endogeneity Check**********************
****************************************************
gen lnday = ln(dday30)
gen dd = lnday*lnday
gen fwd = lnday*lnpf
gen wdl = lnday*lnl 
gen wdr = lnday*lnr
gen wdt = lnday*lnt

reg3 (eq1: lny lnpf lnpw lnpl ff ww ll fw fl wl fr ft wr wt lr lt rr tt rt lnr lnt i.yr i.fips) (eq2: shf lnpf lnpw lnpl lnr lnt i.yr i.fips) (eq3: shw lnpf lnpw lnpl lnr lnt i.yr i.fips) (eq4: shl lnpf lnpw lnpl lnr lnt i.yr i.fips), endog(lnpw ww) exog(lnday dd ) constraint(1-18) ireg3
