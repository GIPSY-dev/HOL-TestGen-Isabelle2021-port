address=http://localhost:$(port)/HealthCare.asmx
wsdl=$(address)?wsdl=0

$(server)/lib/ClientStubs.dll: $(server)/lib/HealthCareStubs.dll $(server)/src/stubs.fs
	$(fcc) -a /r:$(server)/lib/HealthCareStubs.dll $(server)/src/stubs.fs --doc:$(server)/lib/ClietStubs.xml -o $@

$(server)/lib/HealthCareStubs.dll: $(server)/gen/HealthCareStubs.cs
	$(cc) /target:library $^ -out:$@ -r:System.Web.Services

$(server)/gen/HealthCareStubs.cs: $(server)/gen/HealthCare.wsdl
	wsdl -nologo -out:$@ $^ >/dev/null

$(server)/gen/HealthCare.wsdl: $(server)/bin/HealthCareService.dll $(server)/HealthCare.asmx
	wget $(wsdl) -O $@ || rm $@

$(server)/bin/HealthCareService.dll: $(server)/src/monad.fs $(server)/src/core.fs $(server)/src/main.fs $(server)/src/transport.fs 
	$(fcc) -a $^ -o $@ --doc:$(server)/bin/HealthCareService.xml
