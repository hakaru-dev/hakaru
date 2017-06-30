# What is the Hakaru Workflow? #

When you write a Hakaru program, you must follow the workflow of Bayesian inference. Bayesian inference is a method of statistical inference where Bayes' theorem is used
to update the probability of a statistical hypothesis as more information becomes available[^1]. Bayes theorem describes the probability of an event based on knowledge of
event-related conditions[^2].

In Hakaru, the workflow of Bayesian inference appears as *modelling*, *transformation*, and *application* stages[^3]:

1. In the *modelling* stage, you must create a probabilistic model of the environment as a prior probability distribution. This model requires you to include the known 
information and identify what information is to be inferred. The Hakaru language contains distributions and tools which formalize the modelling stage.
2. In the *transformation* stage, the prior distribution created in the modelling stage is transformed into a conditional distribution. During this stage, a function is 
created which maps known knowledge to a distribution that models the information that you want to infer. To automate this stage, Hakaru includes program transformations for 
model conditioning.
3. In the *application* stage, the function generated in the transformation stage is applied to the known knowledge that you have provided to get the posterior distribution
on what is to be inferred. At the end of this stage, you can use Hakaru to show the resulting distribution as both a stream of samples and as a term in the Hakaru language.


[^1]: [Bayesian inference (Wikipedia)](https://en.wikipedia.org/wiki/Bayesian_inference)
[^2]: [Bayes' theorem (Wikipedia)](https://en.wikipedia.org/wiki/Bayes%27_theorem)
[^3]: P. Narayanan, J. Carette, W. Romano, C. Shan and R. Zinkov, "Probabilistic Inference by Program Transformation in Hakaru (System Description)", Functional and Logic 
Programming, pp. 62-79, 2016.