import math

alpha = math.log(3, 2)
I0 = alpha - (alpha*math.log(alpha) - (alpha-1)*math.log(alpha-1))/math.log(2)
theta_p = 1/6 + 1/1000
q = 205198/1080000

print('alpha', alpha, 'I0', I0, 'H2', 1-I0/alpha)
print('Kb/j', q, 'theta_prime', theta_p, 'margin', q-theta_p)
print('pressure_markov', theta_p, 'shape_total_available', q)
print('d c0 kappa_new gamma_cap Pmin18 deltaA~.54/P exponent_saving')
for den in [108,72,54,36,27,18]:
    d=1/den
    c0=1-math.cos(math.pi*d)
    kap=4*c0/3
    gamma=kap*(q-theta_p)/(math.log(2)+kap)
    pmin=18/gamma
    deltaA=.54/pmin
    print(den,c0,kap,gamma,pmin,deltaA,I0*deltaA)

print('phi theta effective and relative margin to theta_prime')
for den in [5,6,7,9,10]:
    phi=1/den
    theta=.1+phi*(.4-.1)
    print(f'1/{den}', theta, theta_p-theta)

print('old/new')
d=1/108
c0=1-math.cos(math.pi*d)
old=8*d*d/133
new=4*c0/3
gnew=new*(q-theta_p)/(math.log(2)+new)
gold=4.85e-8
print(old,new,new/old,gold,gnew,gnew/gold)
