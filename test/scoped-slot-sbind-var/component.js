
const san = require('san')

const Man = san.defineComponent({
    template: '<div><slot name="test" s-bind="{n: data.name, email: \'no@no.com\', sex: \'shemale\'}" var-email="data.email" var-sex="data.sex ? \'male\' : \'female\'"><p>{{n}},{{sex}},{{email}}</p></slot></div>',
    emailClick: function (email) {
        clickInfo.email = 'fail'
        clickInfo.outer = false
    }
})

const MyComponent = san.defineComponent({
    components: {
        'x-man': Man
    },

    template: '<div><x-man data="{{man}}"><h3 slot="test">{{n}}</h3><b slot="test">{{sex}}</b><u slot="test" on-click="emailClick(email)">{{email}}</u></x-man></div>',

    emailClick: function (email) {
        clickInfo.email = email
        clickInfo.outer = true
    }
})

exports = module.exports = MyComponent
