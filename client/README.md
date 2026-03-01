I. DEPLOYING THE ASSERTION-CLIENT

 The prover is running as a cloud service that processes assertion-files
sent using the client 'assertion/Client.class' which comprises a java-package.

The client gets easily deployed on any system where a stable internet connection,
a Java Runtime Environment (JRE, visit www.java.com for more information)
as well as a terminal console (a command prompt) are accessible:

  * place the folder 'assertion' containing 'Client.class' in a folder \<dir\> on your system,
    typing subsequently in a terminal console:
    

                  cd <dir>
                  java assertion.Client <path to an assertion-prover file>


    to transfer \<an assertion-prover file\> to the server for processing.    


For instance, if the file 'misc.ap' resides in the folder \<dir\>/examples then either

      cd <dir>
      java assertion.Client examples/misc.ap

or using backslash on a Windows command prompt:

      cd <dir>
      java assertion.Client examples\misc.ap


requests the server to process the content of 'misc.ap' resulting in responses
being sent back to the client and displayed on the screen.

NOTE: NO DATA gets collected by the server except basic connection related statistics.

There is currently a slot of about 30 seconds for such a request:
the connection to the server gets closed straight when this limit is exceeded.

The limit can however be extended to 120 seconds and more using subscription.


II. SUBSCRIPTION 

 In addition to an extended slot, during the subscribed period
each purchased token entitles a designated client program to

   * accessing a significantly more powerful server

   * receiving proof files for confirmed assertions
     (see https://github.com/quantifier-hub/assertion-prover/blob/main/client_manual.pdf for details).
     

The price of one standard token:  € 55  for 30 days.

Inquiries and questions can be sent to:    assertion@quantifier.cloud 







