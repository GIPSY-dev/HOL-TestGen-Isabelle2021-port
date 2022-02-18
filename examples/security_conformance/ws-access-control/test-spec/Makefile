
fcc=fsharpc --nologo --nowarn:58
cc=gmcs

port=8080
shd=../server/
include ../server/server.mk

bin/HealthCareStubs.dll: $(shd)lib/HealthCareStubs.dll
	cp $^ $@

bin/ClientStubs.dll: $(shd)lib/ClientStubs.dll
	cp $^ $@

bin/ts_prototype.exe: ts_prototype.fs ts_prototype_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts_prototype.fs ts_prototype_run.fs -o $@

bin/ts1.exe: ts1.fs ts1_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts1.fs ts1_run.fs -o $@

bin/ts2.exe: ts2.fs ts2_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts2.fs ts2_run.fs -o $@

bin/ts3.exe: ts3.fs ts3_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts3.fs ts3_run.fs -o $@

bin/ts4.exe: ts4.fs ts4_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts4.fs ts4_run.fs -o $@

bin/ts5.exe: ts5.fs ts5_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts5.fs ts5_run.fs -o $@

bin/ts5a.exe: ts5a.fs ts5a_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts5a.fs ts5a_run.fs -o $@

bin/ts6.exe: ts6.fs ts6_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts6.fs ts6_run.fs -o $@

bin/ts7.exe: ts7.fs ts7_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts7.fs ts7_run.fs -o $@

bin/ts8.exe: ts8.fs ts8_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts8.fs ts8_run.fs -o $@

bin/ts9.exe: ts9.fs ts9_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts9.fs ts9_run.fs -o $@

bin/ts6a.exe: ts6a.fs ts6a_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts6a.fs ts6a_run.fs -o $@

bin/ts9a.exe: ts8a.fs ts8a_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs ts8a.fs ts8a_run.fs -o $@


bin/TalkTest1.exe: TalkTest1.fs TalkTest1_run.fs harnessng.fs bin/HealthCareStubs.dll bin/ClientStubs.dll
	$(fcc) /r:bin/ClientStubs.dll /r:bin/HealthCareStubs.dll harnessng.fs TalkTest1.fs TalkTest1_run.fs -o $@
