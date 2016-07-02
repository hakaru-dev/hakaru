# Examples

### Gaussian Mixture Model

Below is a model for a Gaussian Mixture model. This can be seen
as a Bayesian version of K-means clustering.

````nohighlight
# Prelude to define dirichlet
def add(a prob, b prob):
    a + b

def sum(a array(prob)):
    reduce(add, 0, a)

def normalize(x array(prob)):
    total = sum(x)
    array i of size(x):
       x[i] / total

def dirichlet(as array(prob)):
    xs <~ plate i of int2nat(size(as)-1):
            beta(summate j from 0 to i:
                   as[j], as[i+1])
    return array i of size(as):
             x = product j from i to int2nat(size(as)-2): xs[j]
             x * if i==0: 1 else: real2prob(1-xs[int2nat(i-1)])


# num of clusters
K = 5
# num of points
N = 20

# prior probability of picking cluster K
pi  <~ dirichlet(array _ of K: 1)
# prior on mean and precision
mu  <~ plate _ of K:
         normal(0, 5e-9)
tau <~ plate _ of K:
         gamma(2, 0.05)
# observed data
x   <~ plate _ of N:
         i <~ categorical(pi)
         normal(mu[i], tau[i])

return (x, mu). pair(array(real), array(real))
````

### Latent Dirichlet Allocation

Below is the LDA topic model.

````nohighlight
K = 2 # number of topics
M = 3 # number of docs
V = 7 # size of vocabulary

# number of words in each document
doc = [4, 5, 3]

topic_prior = array _ of K: 1.0
word_prior  = array _ of V: 1.0

phi <~ plate _ of K:     # word dist for topic k
         dirichlet(word_prior)

# likelihood
z   <~ plate m of M:
         theta <~ dirichlet(topic_prior)
         plate _ of doc[m]: # topic marker for word n in doc m
           categorical(theta)

w   <~ plate m of M: # for doc m
         plate n of doc[m]: # for word n in doc m
           categorical(phi[z[m][n]])

return (w, z)
````
