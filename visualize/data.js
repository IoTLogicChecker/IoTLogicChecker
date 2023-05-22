const data = {"nodes": [{"id": "p1", "description": "cloud controls (bind (user Y) (device X) S)", "eternal": true, "operationp": false, "available": true}, {"id": "p2", "description": "cloud controls (flagOnCloudBindingKey (device B) S)", "eternal": true, "operationp": false, "available": true}, {"id": "p3", "description": "deviceB controls (flagOnDeviceBindingKey deviceB S)", "eternal": true, "operationp": false, "available": true}, {"id": "p4", "description": "cloud says (device X transfer (cloud , S) =>\n\t\t\t\t\t\tremove (flagOnCloudBindingKey (device X) ANYS) and\n\t\t\t\t\t\tflagOnCloudBindingKey (device X) S)", "eternal": true, "operationp": false, "available": true}, {"id": "p5", "description": "cloud says (flagOnCloudBindingKey (device X) S =>!\n\t\t\t\t\t\tuser Y transfer(cloud , S) !=>\n            notexist (bind ANYU (device X) ANYS) => (bind (user Y) (device X) S))", "eternal": true, "operationp": false, "available": true}, {"id": "p6", "description": "cloud says (user Z says action (cloud 's (api \"reset\")) =>\n\t\tflagOnCloudBindingKey (device X) S =>!\n    user Z transfer (cloud , S , X) !=>\n    remove (bind ANYU (device X) ANYS))", "eternal": true, "operationp": false, "available": true}, {"id": "p7", "description": "deviceB says (user X says action (deviceB 's button) at (time T) =>\n\tuser X transfer (deviceB , S) until (T + 30) !=>\n\tremove (flagOnDeviceBindingKey deviceB S2) and\n\t(deviceB transfer (cloud , S)) and\n\t(flagOnDeviceBindingKey deviceB S))", "eternal": true, "operationp": false, "available": true}, {"id": "p8", "description": "deviceB says ((flagOnDeviceBindingKey deviceB S) =>!\n\tuser Z says action (deviceB 's button) =>\n\tdeviceB transfer (user Z , S))", "eternal": true, "operationp": false, "available": true}, {"id": "p9", "description": "userC transfer (deviceB , \"RandomStrByuserC\") at (time 0)", "eternal": false, "operationp": true, "available": false}, {"id": "p10", "description": "userC transfer deviceB , \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p11", "description": "userC says (action (deviceB 's button)) at (time 5)", "eternal": false, "operationp": true, "available": false}, {"id": "p12", "description": "userC says action (deviceB 's button)", "eternal": false, "operationp": false, "available": false}, {"id": "p13", "description": "\n   deviceB\n      says (user \"C\" transfer deviceB , X1 until 35\n               !=> remove (flagOnDeviceBindingKey deviceB X2)\n                      and deviceB transfer cloud , X1\n                      and flagOnDeviceBindingKey deviceB X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p14", "description": "userC transfer (deviceB , \"RandomStrByuserC\") at (time 10)", "eternal": false, "operationp": true, "available": false}, {"id": "p15", "description": "userC transfer deviceB , \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p16", "description": "remove (flagOnDeviceBindingKey deviceB X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p17", "description": "deviceB says remove (flagOnDeviceBindingKey deviceB X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p18", "description": "deviceB transfer cloud , \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p19", "description": "deviceB says (deviceB transfer cloud , \"RandomStrByuserC\")", "eternal": false, "operationp": false, "available": false}, {"id": "p20", "description": "deviceB says flagOnDeviceBindingKey deviceB \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p21", "description": "deviceB says flagOnDeviceBindingKey deviceB \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p22", "description": "flagOnDeviceBindingKey deviceB \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p23", "description": "remove (flagOnCloudBindingKey (device \"B\") X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p24", "description": "cloud says remove (flagOnCloudBindingKey (device \"B\") X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p25", "description": "cloud says flagOnCloudBindingKey (device \"B\") \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p26", "description": "cloud says flagOnCloudBindingKey (device \"B\") \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p27", "description": "flagOnCloudBindingKey (device \"B\") \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p28", "description": "\n   deviceB\n      says (user X1 says action (deviceB 's button)\n               => deviceB transfer user X1 , \"RandomStrByuserC\")", "eternal": false, "operationp": false, "available": false}, {"id": "p29", "description": "\n   cloud\n      says (user X1 transfer cloud , \"RandomStrByuserC\"\n               !=> notexist (bind X2 (device \"B\") X3)\n               => bind (user X1) (device \"B\") \"RandomStrByuserC\")", "eternal": false, "operationp": false, "available": false}, {"id": "p30", "description": "userC transfer (cloud , \"RandomStrByuserC\") at (time 15)", "eternal": false, "operationp": true, "available": false}, {"id": "p31", "description": "userC transfer cloud , \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p32", "description": "\n   cloud\n      says (notexist (bind X1 (device \"B\") X2)\n               => bind (user \"C\") (device \"B\") \"RandomStrByuserC\")", "eternal": false, "operationp": false, "available": false}, {"id": "p33", "description": "cloud says (bind (user \"C\") (device \"B\") \"RandomStrByuserC\")", "eternal": false, "operationp": false, "available": false}, {"id": "p34", "description": "bind (user \"C\") (device \"B\") \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": true}, {"id": "p35", "description": "userA says action (deviceB 's button) at (time 20)", "eternal": false, "operationp": true, "available": false}, {"id": "p36", "description": "userA says action (deviceB 's button)", "eternal": false, "operationp": false, "available": false}, {"id": "p37", "description": "\n   deviceB\n      says (user \"A\" transfer deviceB , X1 until 50\n               !=> remove (flagOnDeviceBindingKey deviceB X2)\n                      and deviceB transfer cloud , X1\n                      and flagOnDeviceBindingKey deviceB X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p38", "description": "deviceB transfer user \"A\" , \"RandomStrByuserC\"", "eternal": false, "operationp": false, "available": false}, {"id": "p39", "description": "userA transfer (deviceB , \"password\") at (time 25)", "eternal": false, "operationp": true, "available": false}, {"id": "p40", "description": "userA transfer deviceB , \"password\"", "eternal": false, "operationp": false, "available": false}, {"id": "p41", "description": "remove (flagOnDeviceBindingKey deviceB X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p42", "description": "deviceB says remove (flagOnDeviceBindingKey deviceB X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p43", "description": "deviceB transfer cloud , \"password\"", "eternal": false, "operationp": false, "available": false}, {"id": "p44", "description": "deviceB says (deviceB transfer cloud , \"password\")", "eternal": false, "operationp": false, "available": false}, {"id": "p45", "description": "deviceB says flagOnDeviceBindingKey deviceB \"password\"", "eternal": false, "operationp": false, "available": false}, {"id": "p46", "description": "deviceB says flagOnDeviceBindingKey deviceB \"password\"", "eternal": false, "operationp": false, "available": false}, {"id": "p47", "description": "flagOnDeviceBindingKey deviceB \"password\"", "eternal": false, "operationp": false, "available": true}, {"id": "p48", "description": "remove (flagOnCloudBindingKey (device \"B\") X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p49", "description": "cloud says remove (flagOnCloudBindingKey (device \"B\") X1)", "eternal": false, "operationp": false, "available": false}, {"id": "p50", "description": "cloud says flagOnCloudBindingKey (device \"B\") \"password\"", "eternal": false, "operationp": false, "available": false}, {"id": "p51", "description": "cloud says flagOnCloudBindingKey (device \"B\") \"password\"", "eternal": false, "operationp": false, "available": false}, {"id": "p52", "description": "flagOnCloudBindingKey (device \"B\") \"password\"", "eternal": false, "operationp": false, "available": true}, {"id": "p53", "description": "\n   deviceB\n      says (user X1 says action (deviceB 's button)\n               => deviceB transfer user X1 , \"password\")", "eternal": false, "operationp": false, "available": true}, {"id": "p54", "description": "\n   cloud\n      says (user X1 transfer cloud , \"password\"\n               !=> notexist (bind X2 (device \"B\") X3)\n               => bind (user X1) (device \"B\") \"password\")", "eternal": false, "operationp": false, "available": false}, {"id": "p55", "description": "userA transfer (cloud , \"password\") at (time 30)", "eternal": false, "operationp": true, "available": true}, {"id": "p56", "description": "userA transfer cloud , \"password\"", "eternal": false, "operationp": false, "available": true}, {"id": "p57", "description": "\n   cloud\n      says (notexist (bind X1 (device \"B\") X2)\n               => bind (user \"A\") (device \"B\") \"password\")", "eternal": false, "operationp": false, "available": false}], "edges": [{"source": "p1", "target": "p34"}, {"source": "p2", "target": "p52"}, {"source": "p2", "target": "p27"}, {"source": "p3", "target": "p47"}, {"source": "p3", "target": "p22"}, {"source": "p4", "target": "p50"}, {"source": "p4", "target": "p26"}, {"source": "p4", "target": "p48"}, {"source": "p4", "target": "p49"}, {"source": "p4", "target": "p25"}, {"source": "p4", "target": "p51"}, {"source": "p4", "target": "p23"}, {"source": "p4", "target": "p24"}, {"source": "p5", "target": "p29"}, {"source": "p5", "target": "p54"}, {"source": "p7", "target": "p37"}, {"source": "p7", "target": "p13"}, {"source": "p8", "target": "p28"}, {"source": "p8", "target": "p53"}, {"source": "p9", "target": "p10"}, {"source": "p11", "target": "p12"}, {"source": "p11", "target": "p13"}, {"source": "p13", "target": "p20"}, {"source": "p13", "target": "p17"}, {"source": "p13", "target": "p21"}, {"source": "p13", "target": "p16"}, {"source": "p13", "target": "p18"}, {"source": "p13", "target": "p19"}, {"source": "p14", "target": "p15"}, {"source": "p15", "target": "p20"}, {"source": "p15", "target": "p17"}, {"source": "p15", "target": "p21"}, {"source": "p15", "target": "p16"}, {"source": "p15", "target": "p18"}, {"source": "p15", "target": "p19"}, {"source": "p18", "target": "p23"}, {"source": "p18", "target": "p25"}, {"source": "p18", "target": "p24"}, {"source": "p18", "target": "p26"}, {"source": "p20", "target": "p22"}, {"source": "p22", "target": "p28"}, {"source": "p25", "target": "p27"}, {"source": "p27", "target": "p29"}, {"source": "p28", "target": "p38"}, {"source": "p29", "target": "p32"}, {"source": "p30", "target": "p31"}, {"source": "p31", "target": "p32"}, {"source": "p32", "target": "p33"}, {"source": "p33", "target": "p34"}, {"source": "p35", "target": "p37"}, {"source": "p35", "target": "p36"}, {"source": "p36", "target": "p38"}, {"source": "p37", "target": "p41"}, {"source": "p37", "target": "p44"}, {"source": "p37", "target": "p46"}, {"source": "p37", "target": "p43"}, {"source": "p37", "target": "p42"}, {"source": "p37", "target": "p45"}, {"source": "p39", "target": "p40"}, {"source": "p40", "target": "p41"}, {"source": "p40", "target": "p44"}, {"source": "p40", "target": "p46"}, {"source": "p40", "target": "p43"}, {"source": "p40", "target": "p42"}, {"source": "p40", "target": "p45"}, {"source": "p43", "target": "p49"}, {"source": "p43", "target": "p50"}, {"source": "p43", "target": "p51"}, {"source": "p43", "target": "p48"}, {"source": "p45", "target": "p47"}, {"source": "p47", "target": "p53"}, {"source": "p50", "target": "p52"}, {"source": "p52", "target": "p54"}, {"source": "p54", "target": "p57"}, {"source": "p55", "target": "p56"}, {"source": "p56", "target": "p57"}]}